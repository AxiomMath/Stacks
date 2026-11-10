module

public import Mathlib
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoFromDerivedIso
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.Homology.HomComplex.CochainScalarTower
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
import StacksFrontier.Homology.RelativelyPerfect.CochainBaseChange
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.Complex

/-!
# Faithfully flat descent of dualizing complexes

A complex over a Noetherian ring is dualizing as soon as it becomes dualizing after a
faithfully flat base change to another Noetherian ring.

## Main results

* `Dualizing.isDualizingComplex_of_faithfullyFlat` descends the property of being a dualizing
  complex through a faithfully flat ring map.

## Implementation notes

The existing total derived extension-of-scalars functor represents the derived tensor product
with the target ring. Its module universe is chosen above the independent universes of both
rings.

Each of the three conditions defining a dualizing complex is descended separately. Boundedness
and finiteness of cohomology descend because faithful flatness makes base change reflect both
vanishing and finite generation. For the homothety condition the proof builds, over the target,
a Hom-complex model of the derived endomorphisms and shows that base change of the Hom complex
out of a finite free complex into a bounded complex is bijective, so that the quasi-isomorphism
over the target descends to one over the source.

## References

* [Stacks Project, Tag 0E4A](https://stacks.math.columbia.edu/tag/0E4A)
-/

@[expose] public section

open CategoryTheory DerivedCategory
open CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w z

namespace Dualizing


private theorem subsingleton_of_faithfullyFlat_tensor_subsingleton
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (M : Type z) [AddCommGroup M] [Module A M]
    (hM : Subsingleton (TensorProduct A B M)) : Subsingleton M := by
  let z : M →ₗ[A] M := 0
  have hz : Function.Bijective (z.lTensor B) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hz' : Function.Bijective z :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := A) (M := B) (f := z)).1 hz
  exact ⟨fun x y => hz'.1 (show z x = z y by rfl)⟩


private noncomputable def derivedExtensionScalars_homologyIso
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat.{max v u w} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u w} B) i).obj
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
          f).functor.obj K) ≅
      (ModuleCat.extendScalars.{u, w, max v u w} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K) :=
  (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, w, v}
    f hf i).app K

/-- If the base change of a complex has vanishing `i`-th homology along a faithfully flat ring
map, then so does the complex. -/
private theorem isZero_homology_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} B) i).obj
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K) := by
  let : Algebra A B := f.toAlgebra
  let : Module.FaithfullyFlat A B := hf
  have htensor : IsZero (ModuleCat.of B (TensorProduct A B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K))) :=
    IsZero.of_iso h ((derivedExtensionScalars_homologyIso.{u, v, w} f hf.flat K i).symm)
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (subsingleton_of_faithfullyFlat_tensor_subsingleton (A := A) (B := B) _
      (ModuleCat.isZero_iff_subsingleton.mp htensor))

private theorem baseChange_isGE_reflects
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A)) (a : ℤ)
    (hK : ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
      f).functor.obj K).IsGE a) : K.IsGE a :=
  (DerivedCategory.isGE_iff K a).2 fun i hi =>
    isZero_homology_of_faithfullyFlat f hf K i ((DerivedCategory.isGE_iff _ a).1 hK i hi)

private theorem baseChange_isLE_reflects
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A)) (a : ℤ)
    (hK : ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
      f).functor.obj K).IsLE a) : K.IsLE a :=
  (DerivedCategory.isLE_iff K a).2 fun i hi =>
    isZero_homology_of_faithfullyFlat f hf K i ((DerivedCategory.isLE_iff _ a).1 hK i hi)


private theorem derivedExtensionScalars_isGE
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat.{max v u w} A)) (a : ℤ) (hK : K.IsGE a) :
    ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
      f).functor.obj K).IsGE a := by
  let : Algebra A B := f.toAlgebra
  let F := ModuleCat.extendScalars.{u, w, max v u w} f
  apply (DerivedCategory.isGE_iff _ a).2
  intro i hi
  have hzero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u w} A) i).obj K) :=
    (DerivedCategory.isGE_iff K a).1 hK i hi
  have hmap : IsZero (F.obj ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u w} A) i).obj K)) := by
    change IsZero (ModuleCat.of B (TensorProduct A B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K)))
    let : Subsingleton ((DerivedCategory.homologyFunctor
        (ModuleCat.{max v u w} A) i).obj K) := ModuleCat.isZero_iff_subsingleton.mp hzero
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact IsZero.of_iso hmap
    (derivedExtensionScalars_homologyIso.{u, v, w} f hf K i)

private lemma isLE_mapDerivedCategory
    {R S : Type*} [Ring R] [Ring S]
    (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory (ModuleCat R)) (n : ℤ) (hX : X.IsLE n) :
    (F.mapDerivedCategory.obj X).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero ((DerivedCategory.isLE_iff X n).mp hX i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app X)

private lemma isGE_mapDerivedCategory
    {R S : Type*} [Ring R] [Ring S]
    (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory (ModuleCat R)) (n : ℤ) (hX : X.IsGE n) :
    (F.mapDerivedCategory.obj X).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero ((DerivedCategory.isGE_iff X n).mp hX i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app X)

private lemma homComplexR_isStrictlyLE
    {R : Type u} [CommRing R]
    (F G : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hF : F.IsStrictlyGE a) (hG : G.IsStrictlyLE b) :
    (CochainComplex.HomComplexR R F G).IsStrictlyLE (b - a) := by
  let := hF
  let := hG
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  change IsZero (ModuleCat.of R
    ((CochainComplex.HomComplexR R F G).X i))
  have hs : Subsingleton ((CochainComplex.HomComplexR R F G).X i) := by
    change Subsingleton (CochainComplex.HomComplex.Cochain F G i)
    let : Subsingleton (CochainComplex.HomComplex.Cochain F G i) :=
    ⟨fun x y => by
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      by_cases hp : p < a
      · exact F.isZero_of_isStrictlyGE a p hp |>.eq_of_src _ _
      · have hq : b < q := by omega
        exact G.isZero_of_isStrictlyLE b q hq |>.eq_of_tgt _ _⟩
    exact this
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

private theorem derivedHom_isLE_of_injectiveAmplitude
    {R : Type u} [CommRing R]
    (X Y : DerivedCategory (ModuleCat.{max u v} R)) (n a b : ℤ)
    (hX : X.IsGE n)
    (hY : StacksDraft.InjectiveDimension.HasInjectiveAmplitude Y a b) :
    ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v, (max u v) + 1} R).hom.obj
      (Opposite.op X, Y)).IsLE (b - n) := by
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, max u v, (max u v) + 1} R
  let m := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, max u v} R
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v, (max u v) + 1} R
  let dUL := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, max u v, (max u v) + 1} (R := R)
  let X' := e.inverse.obj X
  let Y' := e.inverse.obj Y
  obtain ⟨I, hIa, hIb, hIi, ⟨eI⟩⟩ := hY
  have hX' : X'.IsGE n := by
    change (m.inverse.mapDerivedCategory.{(max u v) + 1, (max u v) + 1,
      max u v, max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}.obj X).IsGE n
    exact isGE_mapDerivedCategory m.inverse X n hX
  let I' : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} R)) ℤ :=
    (m.inverse.mapHomologicalComplex.{0, max u v, max (u + 1) (v + 1),
      max u v, max (u + 1) (v + 1)} (ComplexShape.up ℤ)).obj I
  have hI'GE : I'.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff I m.inverse a).2 hIa
  have hI'LE : I'.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff I m.inverse b).2 hIb
  have hI'inj : ∀ i : ℤ, Injective (I'.X i) := by
    intro i
    change Injective (ModuleCat.of (ULift.{max u v} R) (I'.X i))
    rw [← Module.injective_iff_injective_object]
    have hI : Module.Injective R (I.X i) :=
      Module.injective_module_of_injective_object R (I.X i)
    let eR : R ≃+* ULift.{max u v} R :=
      (ULift.ringEquiv : ULift.{max u v} R ≃+* R).symm
    let : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eR
    let : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm eR
    let eI' : I.X i ≃ₛₗ[eR.toRingHom] I'.X i := {
      __ := AddEquiv.refl _
      map_smul' := by
        intro r x
        change r • x = ULift.ringEquiv (eR r) • x
        rfl }
    exact Module.Injective.of_ringEquiv eR eI'
  have eI' : Nonempty (Y' ≅ DerivedCategory.Q.obj I') := by
    refine ⟨e.inverse.mapIso eI ≪≫
      (m.inverse.mapDerivedCategoryFactors.{(max u v) + 1,
        (max u v) + 1, max u v, max (u + 1) (v + 1), max u v,
        max (u + 1) (v + 1)}.app I)⟩
  obtain ⟨F, hF, ⟨eF⟩⟩ := X'.exists_iso_Q_obj_of_isGE n
  let : I'.IsStrictlyGE a := hI'GE
  let : I'.IsStrictlyLE b := hI'LE
  let : ∀ i : ℤ, Injective (I'.X i) := hI'inj
  let : I'.IsKInjective := CochainComplex.isKInjective_of_injective I' a
  have hHC : (DerivedCategory.Q.obj
      (CochainComplex.HomComplexR (ULift.{max u v} R) F I')).IsLE (b - n) := by
    let hstrict := homComplexR_isStrictlyLE F I' n b hF hI'LE
    let := hstrict
    infer_instance
  let eModel : dUL.hom.obj (Opposite.op X', Y') ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{max u v} R) F I') :=
    dUL.hom.mapIso (Iso.prod eF.symm.op (Classical.choice eI')) ≪≫
      dUL.homIso F I'
  have hUL : (dUL.hom.obj (Opposite.op X', Y')).IsLE (b - n) :=
    TStructure.t.isLE_of_iso eModel.symm (b - n)
  have hMap : (e.functor.obj (dUL.hom.obj (Opposite.op X', Y'))).IsLE (b - n) := by
    change (m.functor.mapDerivedCategory.obj (dUL.hom.obj (Opposite.op X', Y'))).IsLE (b - n)
    exact isLE_mapDerivedCategory m.functor _ _ hUL
  let eH : d.hom.obj (Opposite.op X, Y) ≅
      e.functor.obj (dUL.hom.obj (Opposite.op X', Y')) :=
    d.hom.mapIso ((e.counitIso.app X).op.prod (e.counitIso.app Y).symm) ≪≫
      (StacksDraft.DerivedHom.derivedHomULiftIso.{u, max u v, (max u v) + 1} R).app
        (Opposite.op X', Y')
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact ((DerivedCategory.isLE_iff _ _).mp hMap i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso eH)

private theorem finiteCohomology_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A))
    (hK : IsDualizingComplex
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor.obj K)) :
    ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K) := by
  intro i
  let : Algebra A B := f.toAlgebra
  let : Module.FaithfullyFlat A B := hf
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
  let H_B := DerivedCategory.homologyFunctor (ModuleCat.{max v u w} B) i
  let eH := derivedExtensionScalars_homologyIso.{u, v, w} f hf.flat K i
  have hfinite : Module.Finite B
      ((ModuleCat.extendScalars.{u, w, max v u w} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K)) := by
    let : Module.Finite B (H_B.obj (D.functor.obj K)) := hK.finiteCohomology i
    exact Module.Finite.equiv eH.toLinearEquiv
  change Module.Finite B
    (TensorProduct A B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj K)) at hfinite
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

private theorem pseudoCoherent_of_bounded_finite_cohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (b : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K))
    (hLE : K.IsLE b) : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    K 0 (ULift.{max v u} A)).2.1.mpr ⟨⟨b, (DerivedCategory.isLE_iff K b).1 hLE⟩, hK⟩

/-- A finite module, placed in degree zero over a Noetherian ring, is pseudo-coherent. -/
@[sga "6 I 5.0" "partial"]
public theorem pseudoCoherent_single_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) 0
      (M : Type v)).2.2.mpr inferInstance

private theorem injectiveAmplitude_shift
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b i : ℤ)
    (hK : StacksDraft.InjectiveDimension.HasInjectiveAmplitude K a b) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude (K⟦i⟧) (a - i) (b - i) := by
  obtain ⟨I, hIa, hIb, hIi, ⟨e⟩⟩ := hK
  let I' := I⟦i⟧
  have hI'a : I'.IsStrictlyGE (a - i) := by
    change ((shiftFunctor (CochainComplex (ModuleCat.{max u v} R) ℤ) i).obj I).IsStrictlyGE _
    exact I.isStrictlyGE_shift a i (a - i) (by omega)
  have hI'b : I'.IsStrictlyLE (b - i) := by
    change ((shiftFunctor (CochainComplex (ModuleCat.{max u v} R) ℤ) i).obj I).IsStrictlyLE _
    exact I.isStrictlyLE_shift b i (b - i) (by omega)
  have hI'i : ∀ n : ℤ, Injective (I'.X n) := by
    intro n
    change Injective (I.X (n + i))
    exact hIi (n + i)
  have e' : K⟦i⟧ ≅ DerivedCategory.Q.obj I' :=
    (shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) i).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso i).symm.app I
  exact ⟨I', hI'a, hI'b, hI'i, ⟨e'⟩⟩

private theorem homComplex_represents_derivedHom_general
    {R : Type u} [CommRing R]
    (L I : CochainComplex (ModuleCat.{v} R) ℤ) (a n : ℤ)
    [I.IsStrictlyGE a] [∀ i : ℤ, Injective (I.X i)] :
    Function.Bijective
      (fun (c : CochainComplex.HomComplex.CohomologyClass L I n) ↦
        DerivedCategory.Qh.map
          (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c)) := by
  let I' := I⟦n⟧
  have hI' : I'.IsStrictlyGE (a - n) := by
    change ((shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n).obj I).IsStrictlyGE _
    exact I.isStrictlyGE_shift a n (a - n) (by omega)
  have hIi' : ∀ i : ℤ, Injective (I'.X i) := by
    intro i
    change Injective (I.X (i + n))
    exact ‹∀ i : ℤ, Injective (I.X i)› (i + n)
  let : I'.IsStrictlyGE (a - n) := hI'
  let : ∀ i : ℤ, Injective (I'.X i) := hIi'
  have : I'.IsKInjective := CochainComplex.isKInjective_of_injective I' (a - n)
  exact (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ _).obj L) I').comp
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := L) (L := I) (n := n)).bijective

private theorem hom_ext_subsingleton_of_derivedHom_isLE
    {R : Type u} [CommRing R]
    (X Y : DerivedCategory (ModuleCat.{max u v} R)) (a n : ℤ)
    (hY : Y.IsGE a)
    (hHom : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
        max u v + 1} R).hom.obj
      (Opposite.op X, Y)).IsLE n) (hn : n < 0) :
    Subsingleton (X ⟶ Y) := by
  let m := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, max u v} R
  let e := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, max u v, max u v + 1} R
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} R
  let dUL := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, max u v, max u v + 1}
    (R := R)
  let X' := e.inverse.obj X
  let Y' := e.inverse.obj Y
  have hY' : Y'.IsGE a := by
    change (m.inverse.mapDerivedCategory.obj Y).IsGE a
    exact isGE_mapDerivedCategory m.inverse Y a hY
  let E := dUL.hom.obj (Opposite.op X', Y')
  have hE : E.IsLE n := by
    let eH : d.hom.obj (Opposite.op X, Y) ≅ e.functor.obj E :=
      d.hom.mapIso ((e.counitIso.app X).op.prod (e.counitIso.app Y).symm) ≪≫
        (StacksDraft.DerivedHom.derivedHomULiftIso.{u, max u v,
          max u v + 1} R).app (Opposite.op X', Y')
    let : (d.hom.obj (Opposite.op X, Y)).IsLE n := hHom
    have hMap : (e.functor.obj E).IsLE n := TStructure.t.isLE_of_iso eH n
    have hMap' : (m.inverse.mapDerivedCategory.obj (e.functor.obj E)).IsLE n :=
      isLE_mapDerivedCategory m.inverse (e.functor.obj E) n hMap
    change ((e.functor ⋙ e.inverse).obj E).IsLE n at hMap'
    let : ((e.functor ⋙ e.inverse).obj E).IsLE n := hMap'
    exact TStructure.t.isLE_of_iso (e.unitIso.app E).symm n
  let L := DerivedCategory.Q.objPreimage X'
  have eL : DerivedCategory.Q.obj L ≅ X' := DerivedCategory.Q.objObjPreimageIso X'
  obtain ⟨L₀, hL₀, ⟨eY⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE Y' a
  obtain ⟨I₀, hI₀, f, hf⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ⟨L₀, a, hL₀⟩ a
  have : QuasiIso f.hom := hf
  let C := ModuleCat.{max u v} (ULift.{max u v} R)
  let I : CochainComplex C ℤ :=
    ((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj I₀.obj
  have hI : I.IsStrictlyGE a := by
    let : I₀.obj.IsStrictlyGE a := hI₀
    infer_instance
  have hIi : ∀ i : ℤ, Injective (I.X i) := by
    intro i
    exact inferInstanceAs (Injective ((InjectiveObject.ι C).obj (I₀.obj.X i)))
  have eI : Y' ≅ DerivedCategory.Q.obj I :=
    eY ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map f.hom)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C f.hom).mpr hf)
  let H := CochainComplex.HomComplexR (ULift.{max u v} R) L I
  let eModel : E ≅ DerivedCategory.Q.obj H :=
    dUL.hom.mapIso (Iso.prod eL.op eI) ≪≫ dUL.homIso L I
  have hzeroE : IsZero
      ((DerivedCategory.homologyFunctor C 0).obj E) :=
    DerivedCategory.isZero_of_isLE E n 0 (by omega)
  have hzeroQH : IsZero ((DerivedCategory.homologyFunctor C 0).obj
      (DerivedCategory.Q.obj H)) :=
    IsZero.of_iso hzeroE ((DerivedCategory.homologyFunctor C 0).mapIso eModel).symm
  have hzeroH : IsZero
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).obj H) :=
    IsZero.of_iso hzeroQH
      ((DerivedCategory.homologyFunctorFactors C 0).app H).symm
  have hclass : Subsingleton (CochainComplex.HomComplex.CohomologyClass L I 0) := by
    let V := forget₂ C AddCommGrpCat
    let eV : (H.homology 0) ≃+ (L.HomComplex I).homology 0 :=
      ((H.sc 0).mapHomologyIso V).symm.addCommGroupIsoToAddEquiv
    let eHC := eV.trans (CochainComplex.HomComplex.homologyAddEquiv L I 0)
    have hzeroHC : Subsingleton (H.homology 0) :=
      ModuleCat.isZero_iff_subsingleton.mp hzeroH
    exact ⟨fun x y => by
      have hp := hzeroHC.elim (eHC.symm x) (eHC.symm y)
      simpa using congrArg eHC hp⟩
  have hbij := homComplex_represents_derivedHom_general L I a 0
  have hX'Y' : ∀ g : X' ⟶ Y', g = 0 := by
    intro g
    let Qh := DerivedCategory.Qh (C := C)
    let qg := (DerivedCategory.quotientCompQhIso C).hom.app L ≫
      (eL.hom ≫ g ≫ eI.hom) ≫ (DerivedCategory.quotientCompQhIso C).inv.app I
    let qshift := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app I)
    have hq : qg = 0 := by
      have hq0 : qg ≫ Qh.map qshift = 0 := by
        obtain ⟨c, hc⟩ := hbij.surjective (qg ≫ Qh.map qshift)
        have hc0 : c = 0 := hclass.elim c 0
        subst c
        simpa using hc.symm
      apply (cancel_mono (Qh.map qshift)).mp
      simpa only [zero_comp] using hq0
    have hq' : (DerivedCategory.quotientCompQhIso C).hom.app L ≫
        (eL.hom ≫ g ≫ eI.hom) ≫ (DerivedCategory.quotientCompQhIso C).inv.app I = 0 := hq
    have hq'' : eL.hom ≫ g ≫ eI.hom = 0 := by
      apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app L)).mp
      apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).inv.app I)).mp
      simpa only [Category.assoc, comp_zero, zero_comp] using hq'
    apply (cancel_mono eI.hom).mp
    apply (cancel_epi eL.hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hq''
  exact ⟨fun g h => e.inverse.map_injective (by
    rw [hX'Y' (e.inverse.map g), hX'Y' (e.inverse.map h)])⟩

private theorem derivedHom_isLE_reflects
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (X Y : DerivedCategory (ModuleCat.{max v u w} A)) (n : ℤ)
    (hBC : IsIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w} A B _
      _ f
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).comparison
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).isLeftDerived X Y))
    (hB : ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, max v u w, max v u w + 1} B).obj
      (Opposite.op ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor.obj X),
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
          f).functor.obj Y)).IsLE n) :
    ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u w, max v u w + 1} A).obj
      (Opposite.op X, Y)).IsLE n := by
  let : Algebra A B := f.toAlgebra
  let : Module.FaithfullyFlat A B := hf
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
  let : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (.up ℤ)) := D.isLeftDerived
  let E := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u w,
    max v u w + 1} A).obj (Opposite.op X, Y)
  let E_B := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, max v u w,
    max v u w + 1} B).obj (Opposite.op (D.functor.obj X), D.functor.obj Y)
  let : IsIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w} A B _ _
    f
      D.functor D.comparison D.isLeftDerived X Y) := hBC
  apply (DerivedCategory.isLE_iff E n).2
  intro i hi
  refine isZero_homology_of_faithfullyFlat f hf E i (IsZero.of_iso
    (DerivedCategory.isZero_of_isLE E_B n i hi)
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} B) i).mapIso
      (asIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w} A B _ _
        f D.functor D.comparison D.isLeftDerived X Y))))

section
open CochainComplex CochainComplex.HomComplex
open StacksDraft.RelativelyPerfect
open scoped ModuleCat.Algebra ChangeOfRings TensorProduct
noncomputable section
/-- Extension of scalars along a ring map `f : A →+* B` is an additive functor
`ModuleCat A ⥤ ModuleCat B`. -/
local instance extendScalars_additive_cochain {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u, v, w} f).Additive := by
  constructor
  intro X Y g h
  apply ModuleCat.hom_ext
  let _ := f.toAlgebra
  exact LinearMap.baseChange_add g.hom h.hom

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

private lemma homComplexMap_δ {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n m : ℤ)
    (z : Cochain K L n) :
    δ n m ((f.f n).hom z) = (f.f m).hom (δ n m z) :=
  ConcreteCategory.congr_hom (f.comm n m) z

private def homCocyclesMap {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    Cocycle K L n →+ Cocycle K' L' n where
  toFun z := ⟨(f.f n).hom (z : Cochain K L n), by
    change δ n (n + 1) ((f.f n).hom (z : Cochain K L n)) = 0
    rw [homComplexMap_δ f n (n + 1) (z : Cochain K L n), z.δ_eq_zero]
    exact (f.f (n + 1)).hom.map_zero⟩
  map_zero' := Subtype.ext (f.f n).hom.map_zero
  map_add' x y := Subtype.ext ((f.f n).hom.map_add (x : Cochain K L n) (y : Cochain K L n))

private def homClassesMap {R : Type u} [CommRing R] {K L K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L' n).comp (homCocyclesMap f n)) (by
      rintro z ⟨m, hm, b, hb⟩
      change CohomologyClass.mk (homCocyclesMap f n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
      refine ⟨(f.f m).hom b, ?_⟩
      change δ m n ((f.f m).hom b) = (f.f n).hom (z : Cochain K L n)
      rw [homComplexMap_δ f m n b, hb])

private def homLeftHomologyMapData {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map f))
      (leftHomologyData K L n) (leftHomologyData K' L' n) := by
  let F := ((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map f
  refine { φK := AddCommGrpCat.ofHom (homCocyclesMap f n)
           φH := AddCommGrpCat.ofHom (homClassesMap f n)
           commi := ?_, commf' := ?_, commπ := ?_ }
  · ext z; rfl
  · have hi : AddCommGrpCat.ofHom (homCocyclesMap f n) ≫
          (leftHomologyData K' L' n).i =
        (leftHomologyData K L n).i ≫ F.f n := by ext z; rfl
    -- `leftHomologyData K L n` is indexed by `(K.HomComplex L).sc n`, which the short-complex
    -- functor's value is only definitionally equal to, so `rw` cannot build a type-correct
    -- motive here; the reassociations and cancellations are taken as terms instead.
    have hcomm :=
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map F).comm₁₂
    refine (cancel_mono (leftHomologyData K' L' n).i).1 ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => (leftHomologyData K L n).f' ≫ z) hi).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ F.f n)
      (ShortComplex.LeftHomologyData.f'_i (leftHomologyData K L n))).trans ?_
    refine hcomm.symm.trans ?_
    refine (congrArg
      (fun z => ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map F).τ₁ ≫ z)
      (ShortComplex.LeftHomologyData.f'_i (leftHomologyData K' L' n)).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  · ext z; rfl

private lemma homClassesMap_precomp {R : Type u} [CommRing R]
    {K K' L : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) (n : ℤ) (z : Cocycle K L n) :
    homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

private lemma homClassesMap_postcomp {R : Type u} [CommRing R]
    {K L L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : L ⟶ L') (n : ℤ) (z : Cocycle K L n) :
    homClassesMap (Stacks.HomComplex.TensorHomMap.postcomp R K L L' f) n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp f) := rfl

private lemma homClassesMap_precomp_toHom {R : Type u} [CommRing R]
    {K K' L : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n z) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesMap_precomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]
  rfl

private lemma homClassesMap_postcomp_toHom {R : Type u} [CommRing R]
    {K L L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : L ⟶ L') (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesMap (Stacks.HomComplex.TensorHomMap.postcomp R K L L' f) n z) =
      CohomologyClass.toHom z ≫ (HomotopyCategory.quotient _ _).map (f⟦n⟧') := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesMap_postcomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
  rfl

private lemma homComplex_quasiIso_iff {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') :
    QuasiIso f ↔ ∀ n, Function.Bijective (homClassesMap f n) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat), quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff, (homLeftHomologyMapData f n).quasiIso_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

private lemma homClassesMap_precomp_bijective {R : Type u} [CommRing R]
    {K K' I : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) (n : ℤ)
    (hf : Function.Bijective (fun g : (HomotopyCategory.quotient _ _).obj K ⟶
        (HomotopyCategory.quotient _ _).obj (I⟦n⟧) =>
      (HomotopyCategory.quotient _ _).map f ≫ g)) :
    Function.Bijective (homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) n) := by
  apply (Function.Bijective.of_comp_iff' (CohomologyClass.toHom_bijective K' I n) _).1
  simpa only [Function.comp_def, homClassesMap_precomp_toHom] using
    hf.comp (CohomologyClass.toHom_bijective K I n)

private lemma precomp_quasiIso_of_isKInjective {R : Type u} [CommRing R]
    {K K' I : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) [QuasiIso f] [I.IsKInjective] :
    QuasiIso (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) := by
  rw [homComplex_quasiIso_iff]
  intro n
  apply homClassesMap_precomp_bijective
  have hI := IsKInjective.rightOrthogonal (I⟦n⟧)
  rw [← ObjectProperty.isLocal_trW] at hI
  apply hI
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (inferInstance : QuasiIso f)


private lemma postcomp_quasiIso_of_isKProjective
    {R : Type u} [CommRing R] {P I J : CochainComplex (ModuleCat.{v} R) ℤ}
    (q : I ⟶ J) [QuasiIso q] [P.IsKProjective] :
    QuasiIso (Stacks.HomComplex.TensorHomMap.postcomp R P I J q) := by
  rw [homComplex_quasiIso_iff]
  intro n
  let e₁ := (CohomologyClass.homAddEquiv (K := P) (L := I) (n := n)).trans
    (qhMapAddEquivOfBijective (CochainComplex.IsKProjective.Qh_map_bijective P _))
  let e₂ := (CohomologyClass.homAddEquiv (K := P) (L := J) (n := n)).trans
    (qhMapAddEquivOfBijective (CochainComplex.IsKProjective.Qh_map_bijective P _))
  apply (Function.Bijective.of_comp_iff' e₂.bijective _).1
  have h : Function.Bijective (fun z : CohomologyClass P I n =>
      DerivedCategory.Qh.map (CohomologyClass.toHom z) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (q⟦n⟧'))) :=
    ((asIso _).homToEquiv.bijective).comp e₁.bijective
  simpa only [Function.comp_def, e₂, AddEquiv.trans_apply,
    qhMapAddEquivOfBijective_apply, CohomologyClass.homAddEquiv_apply,
    homClassesMap_postcomp_toHom, Functor.map_comp] using h

private def scalarHomMap {A : Type u} [CommRing A]
    {P I : CochainComplex (ModuleCat.{max u v} A) ℤ} (p : P ⟶ I) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj
      (ModuleCat.of A (ULift.{max u v} A)) ⟶ HomComplexR A P I :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom ((LinearMap.toSpanSingleton A (Cochain P I 0) (Cochain.ofHom p)).comp
      ULift.moduleEquiv.toLinearMap))
    (fun k hk => by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      ext a
      change δ 0 1 (a.down • Cochain.ofHom p) = 0
      simp)

private lemma scalarHomMap_precomp {A : Type u} [CommRing A]
    {P L I : CochainComplex (ModuleCat.{max u v} A) ℤ} (p : P ⟶ L) (q : L ⟶ I) :
    scalarHomMap q ≫ Stacks.HomComplex.TensorHomMap.precomp A P L I p = scalarHomMap (p ≫ q) := by
  apply HomologicalComplex.from_single_hom_ext
  ext a
  change (Cochain.ofHom p).comp (a.down • Cochain.ofHom q) (zero_add 0) =
    a.down • Cochain.ofHom (p ≫ q)
  rw [Cochain.comp_smul, Cochain.ofHom_comp]

private lemma scalarHomMap_postcomp {A : Type u} [CommRing A]
    {P I J : CochainComplex (ModuleCat.{max u v} A) ℤ} (p : P ⟶ I) (q : I ⟶ J) :
    scalarHomMap p ≫ Stacks.HomComplex.TensorHomMap.postcomp A P I J q = scalarHomMap (p ≫ q) := by
  apply HomologicalComplex.from_single_hom_ext
  ext a
  change (a.down • Cochain.ofHom p).comp (Cochain.ofHom q) (add_zero 0) =
    a.down • Cochain.ofHom (p ≫ q)
  rw [Cochain.smul_comp, Cochain.ofHom_comp]

private def homComplexUnliftIso {A : Type u} [CommRing A]
    (P I : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ((AddCommGrpCat.uliftFunctor.{u, max u v}).mapHomologicalComplex (.up ℤ)).obj
      (HomComplex P I) ≅ HomComplex P I :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => AddEquiv.toAddCommGrpIso AddEquiv.ulift)
    (by intros; rfl)

private lemma scalarHomMap_quasiIso_iff {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    QuasiIso (scalarHomMap (𝟙 I)) ↔ QuasiIso (homothety I) := by
  let F := (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)
  let e := ((forget₂ (ModuleCat.{max u v} A) AddCommGrpCat).mapCochainComplexSingleFunctor 0).app
    (ModuleCat.of A (ULift.{max u v} A))
  have heq : homothety I ≫ (homComplexUnliftIso I I).hom =
      e.inv ≫ F.map (scalarHomMap.{u, v} (𝟙 I)) := by
    apply HomologicalComplex.from_single_hom_ext
    ext a
    simp [e, F, scalarHomMap, homothety, homComplexUnliftIso,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex,
      HomologicalComplex.single]
    rfl
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (scalarHomMap (𝟙 I)) (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat)]
  change QuasiIso (F.map (scalarHomMap (𝟙 I))) ↔ _
  rw [← quasiIso_iff_comp_left e.inv, ← heq]
  let : QuasiIso (homComplexUnliftIso I I).hom := quasiIso_of_isIso _
  exact quasiIso_iff_comp_right (homothety I) (homComplexUnliftIso I I).hom

private def unitBaseChangeIso {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) :
    ((ModuleCat.extendScalars.{u, w, max u v w} f).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{max u v w} A) 0).obj
        (ModuleCat.of A (ULift.{max u v w} A))) ≅
    (CochainComplex.singleFunctor (ModuleCat.{max u v w} B) 0).obj
      (ModuleCat.of B (ULift.{max u v w} B)) := by
  let := f.toAlgebra
  let e : (B ⊗[A] ULift.{max u v w} A) ≃ₗ[B] ULift.{max u v w} B :=
    (ULift.moduleEquiv.baseChange A B).trans
      ((TensorProduct.AlgebraTensorModule.rid A B B).trans ULift.moduleEquiv.symm)
  exact ((ModuleCat.extendScalars f).mapCochainComplexSingleFunctor 0).app
      (ModuleCat.of A (ULift.{max u v w} A)) ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{max u v w} B) 0).mapIso e.toModuleIso

private lemma unitBaseChangeIso_inv_zero_apply
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (x : ULift.{max u v w} B) :
    ((unitBaseChangeIso.{u, v, w} f).inv.f 0) x =
      x.down ⊗ₜ[A, f] (ULift.up (1 : A)) := by
  let := f.toAlgebra
  change ((ULift.moduleEquiv (R := A) (M := A) : ULift.{max u v w} A ≃ₗ[A] A).baseChange A B).symm
    ((TensorProduct.AlgebraTensorModule.rid A B B).symm x.down) = _
  rw [TensorProduct.AlgebraTensorModule.rid_symm_apply,
    ← LinearEquiv.baseChange_symm, LinearEquiv.baseChange_tmul]
  rfl

-- Comparing the scalar maps unfolds both the tensor-unit and single-complex isomorphisms.
private lemma scalarHomMap_baseChange
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) {P I : CochainComplex (ModuleCat.{max u v w} A) ℤ}
    (p : P ⟶ I) :
    (unitBaseChangeIso.{u, v, w} f).inv ≫
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
        (scalarHomMap.{u, max v w} p) ≫
      homComplexBaseChange f P I =
    scalarHomMap.{w, max u v}
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map p) := by
  let := f.toAlgebra
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ULift.{max u v w} B at x
  let g : ULift.{max u v w} A →ₗ[A] Cochain P I 0 :=
    (LinearMap.toSpanSingleton A (Cochain P I 0) (Cochain.ofHom p)).comp
      ULift.moduleEquiv.toLinearMap
  change homCochainBaseChange f P I 0
      ((LinearMap.baseChange B g)
        (((unitBaseChangeIso.{u, v, w} f).inv.f 0) x)) =
    x.down • Cochain.ofHom (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map p)
  have hu := unitBaseChangeIso_inv_zero_apply.{u, v, w} f x
  have hu' := congrArg (fun t : B ⊗[A] ULift.{max u v w} A =>
    homCochainBaseChange f P I 0
      ((LinearMap.baseChange B g) t)) hu
  refine hu'.trans ?_
  rw [LinearMap.baseChange_tmul]
  have hg : g (ULift.up (1 : A)) = Cochain.ofHom p := by simp [g]
  rw [hg]
  change (LinearMap.liftBaseChange B (homCochainExtendScalars f P I 0))
    (x.down ⊗ₜ[A] Cochain.ofHom p) = _
  rw [LinearMap.liftBaseChange_tmul]
  change x.down • (Cochain.ofHom p).map (ModuleCat.extendScalars f) =
    x.down • Cochain.ofHom (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map p)
  rw [Cochain.map_ofHom]


private lemma scalarHomMap_quasiIso_of_baseChange
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    {P I : CochainComplex (ModuleCat.{max u v w} A) ℤ} (p : P ⟶ I) (a b : ℤ)
    [I.IsStrictlyGE a] [I.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    (hp : QuasiIso (scalarHomMap.{w, max u v}
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map p))) :
    QuasiIso (scalarHomMap.{u, max v w} p) := by
  let F := ModuleCat.extendScalars.{u, w, max u v w} f
  let := f.toAlgebra
  let : Module.FaithfullyFlat A B := hf
  let : F.PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact B hS
  let : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  let : F.ReflectsIsomorphisms := by
    refine ⟨fun {M N} g hg => ?_⟩
    rw [ConcreteCategory.isIso_iff_bijective] at hg ⊢
    exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
      (R := A) (M := B) (f := g.hom)).mp hg
  let (n : ℤ) : IsIso ((homComplexBaseChange f P I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (homCochainBaseChange_bijective f P I a b n)
  let : IsIso (homComplexBaseChange f P I) := HomologicalComplex.Hom.isIso_of_components _
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (scalarHomMap.{u, max v w} p) F]
  have hc : QuasiIso ((unitBaseChangeIso.{u, v, w} f).inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map (scalarHomMap.{u, max v w} p) ≫
        homComplexBaseChange f P I) := by
    rw [scalarHomMap_baseChange]
    exact hp
  exact (quasiIso_iff_comp_left _ _).mp ((quasiIso_iff_comp_right _ _).mp (by
    simpa only [Category.assoc] using hc))

private lemma exists_quasiIso_to_kInjective_of_derived_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (L I : CochainComplex C ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) :
    ∃ q : L ⟶ I, QuasiIso q := by
  let ι := DerivedCategory.quotientCompQhIso C
  let e' := ι.app L ≪≫ e ≪≫ (ι.app I).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj L) I).surjective e'.hom
  obtain ⟨q, hq⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
  refine ⟨q, ?_⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  refine (NatIso.isIso_map_iff ι q).1 ?_
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map q))
  rw [hq, hf]
  infer_instance

private lemma homothetyQuasiIso_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hK : IsDualizingComplex
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor.obj K)) : IsDerivedHomothetyQuasiIso K := by
  let F := ModuleCat.extendScalars.{u, w, max v u w} f
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
  let : F.PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology.{u, w, max v u w} f hf.flat
  let : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (.up ℤ)) := D.isLeftDerived
  let : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max v u w} A) (.up ℤ)) (by
      intro X Y g hg
      let : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map (Fc.map g))
      infer_instance)
  obtain ⟨P, hP, ⟨eP⟩⟩ := hP
  obtain ⟨d, hd⟩ := hP.upperBound
  let : P.IsStrictlyLE d := hd
  let (i : ℤ) : Module.Finite A (P.X i) := (hP.finiteFree i).1
  let (i : ℤ) : Module.Free A (P.X i) := (hP.finiteFree i).2
  let (i : ℤ) : Projective (P.X i) := inferInstance
  let (i : ℤ) : Projective ((Fc.obj P).X i) := by
    change Projective (F.obj (P.X i))
    exact (ModuleCat.extendRestrictScalarsAdj f).map_projective (P.X i) inferInstance
  let : CochainComplex.IsStrictlyLE (Fc.obj P) d := inferInstance
  let : CochainComplex.IsKProjective (Fc.obj P) := CochainComplex.isKProjective_of_projective _ d
  obtain ⟨aJ, bJ, J, hJa, hJb, hJinj, ⟨eJ⟩⟩ := hK.finiteInjectiveDimension
  let : J.IsStrictlyGE aJ := hJa
  let (i : ℤ) : Injective (J.X i) := hJinj i
  let : J.IsKInjective := CochainComplex.isKInjective_of_injective J aJ
  have hJ : QuasiIso (scalarHomMap.{w, max u v} (𝟙 J)) :=
    (scalarHomMap_quasiIso_iff.{w, max u v} J).mpr
      (hK.homothetyQuasiIso J ⟨eJ.symm⟩ hJinj ⟨aJ, bJ, hJa, hJb⟩)
  let : QuasiIso (scalarHomMap.{w, max u v} (𝟙 J)) := hJ
  intro I ⟨eI⟩ hIinj ⟨aI, bI, hIa, hIb⟩
  let : I.IsStrictlyGE aI := hIa
  let : I.IsStrictlyLE bI := hIb
  let (i : ℤ) : Injective (I.X i) := hIinj i
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I aI
  obtain ⟨p, hp⟩ := CochainComplex.exists_quasiIso_of_derived_iso P I d (eP ≪≫ eI.symm)
  let : QuasiIso p := hp
  let eIJ : DerivedCategory.Q.obj (Fc.obj I) ≅ DerivedCategory.Q.obj J :=
    (asIso (D.comparison.app I)).symm ≪≫ D.functor.mapIso eI ≪≫ eJ
  obtain ⟨q, hq⟩ := exists_quasiIso_to_kInjective_of_derived_iso (Fc.obj I) J eIJ
  let : QuasiIso q := hq
  let : QuasiIso (Fc.map p) := inferInstance
  let : QuasiIso (Fc.map p ≫ q) := inferInstance
  let : QuasiIso (Stacks.HomComplex.TensorHomMap.precomp B (Fc.obj P) J J (Fc.map p ≫ q)) :=
    precomp_quasiIso_of_isKInjective _
  have hcomp : QuasiIso (scalarHomMap.{w, max u v} (Fc.map p ≫ q)) := by
    have hh := scalarHomMap_precomp.{w, max u v} (Fc.map p ≫ q) (𝟙 J)
    simp only [Category.comp_id] at hh
    rw [← hh]
    exact quasiIso_comp _ _
  let : QuasiIso (Stacks.HomComplex.TensorHomMap.postcomp B (Fc.obj P) (Fc.obj I) J q) :=
    postcomp_quasiIso_of_isKProjective q
  have hpB : QuasiIso (scalarHomMap.{w, max u v} (Fc.map p)) := by
    apply (quasiIso_iff_comp_right _ (Stacks.HomComplex.TensorHomMap.postcomp B (Fc.obj P) (Fc.obj
      I) J q)).mp
    rw [scalarHomMap_postcomp]
    exact hcomp
  have hpA : QuasiIso (scalarHomMap.{u, max v w} p) :=
    scalarHomMap_quasiIso_of_baseChange.{u, v, w} f hf p aI bI hpB
  let : QuasiIso (Stacks.HomComplex.TensorHomMap.precomp A P I I p) :=
    precomp_quasiIso_of_isKInjective p
  apply (scalarHomMap_quasiIso_iff.{u, max v w} I).mp
  apply (quasiIso_iff_comp_right _ (Stacks.HomComplex.TensorHomMap.precomp A P I I p)).mp
  rw [scalarHomMap_precomp, Category.comp_id]
  exact hpA

end

end

/-- **Stacks Project, Tag 0E4A.** If a complex becomes dualizing after faithfully flat
base change between Noetherian rings, then it was already dualizing. -/
@[stacks 0E4A]
public theorem isDualizingComplex_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{max v u w} A))
    (hK : IsDualizingComplex
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
        f).functor.obj K)) :
    IsDualizingComplex K := by
  let K_B : DerivedCategory (ModuleCat.{max v u w} B) :=
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w}
      f).functor.obj K
  obtain ⟨aB, bB, hAmpB⟩ := hK.finiteInjectiveDimension
  rcases hAmpB with ⟨I_B, hIgeB, hIleB, hIinjB, ⟨eB⟩⟩
  have hIBge : I_B.IsGE aB := by
    let := hIgeB
    infer_instance
  have hIBle : I_B.IsLE bB := by
    let := hIleB
    infer_instance
  have hQgeB : (DerivedCategory.Q.obj I_B).IsGE aB :=
    (DerivedCategory.isGE_Q_obj_iff I_B aB).2 hIBge
  have hQleB : (DerivedCategory.Q.obj I_B).IsLE bB :=
    (DerivedCategory.isLE_Q_obj_iff I_B bB).2 hIBle
  have hGE_B : K_B.IsGE aB := TStructure.t.isGE_of_iso eB.symm aB
  have hLE_B : K_B.IsLE bB := TStructure.t.isLE_of_iso eB.symm bB
  have hGE_A := baseChange_isGE_reflects f hf K aB hGE_B
  have hLE_A := baseChange_isLE_reflects f hf K bB hLE_B
  let : K.IsGE aB := hGE_A
  have hAmpB : StacksDraft.InjectiveDimension.HasInjectiveAmplitude K_B aB bB :=
    ⟨I_B, hIgeB, hIleB, hIinjB, ⟨eB⟩⟩
  have hcohA := finiteCohomology_of_faithfullyFlat f hf K hK
  have hFID : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K := by
    let KPlus : DerivedCategory.Plus (ModuleCat.{max v u w} A) := ⟨K, aB, hGE_A⟩
    have hcohPlus : ∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u w} A) i).obj
          (DerivedCategory.Plus.ι.obj KPlus)) := by
      intro i
      simpa [KPlus] using hcohA i
    apply (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_quotient_ext_vanishing
      (⊥ : Ideal A) bot_le KPlus hcohPlus).2
    refine ⟨bB, ?_⟩
    intro J hJ i hi
    let Q_A : DerivedCategory (ModuleCat.{max v u w} A) :=
      (DerivedCategory.singleFunctor (ModuleCat.{max v u w} A) 0).obj
        (ModuleCat.of A (Shrink.{max v u w, u} (A ⧸ J)))
    let Y_A := K⟦i⟧
    have hQpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent Q_A :=
      pseudoCoherent_single_of_finite.{u, max v u w} (ModuleCat.of A
        (Shrink.{max v u w, u} (A ⧸ J)))
    have hQgeA : Q_A.IsGE 0 := by
      dsimp [Q_A]
      infer_instance
    have hYgeA : Y_A.IsGE (aB - i) := by
      change (K⟦i⟧).IsGE (aB - i)
      exact TStructure.t.isGE_shift K aB i (aB - i) (by omega)
    let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
    let Q_B := D.functor.obj Q_A
    let Y_B := D.functor.obj Y_A
    have hQgeB : Q_B.IsGE 0 := derivedExtensionScalars_isGE f hf.flat Q_A 0 hQgeA
    have hBC : IsIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max v u w} A
      B _ _ f
        D.functor D.comparison D.isLeftDerived Q_A Y_A) := by
      let : D.functor.IsLeftDerivedFunctor D.comparison
          (HomologicalComplex.quasiIso (ModuleCat.{max v u w} A) (.up ℤ)) := D.isLeftDerived
      apply @Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, w, max v u w}
        A B _ _ f D.functor D.comparison D.isLeftDerived Q_A Y_A
      exact Or.inr (Or.inr (Or.inl ⟨hf.flat, hQpseudo, ⟨aB - i, hYgeA⟩⟩))
    have hAmpYB : StacksDraft.InjectiveDimension.HasInjectiveAmplitude
        (D.functor.obj Y_A) (aB - i) (bB - i) := by
      obtain ⟨J, hJa, hJb, hJinj, ⟨eJ⟩⟩ :=
        injectiveAmplitude_shift.{w, max v u w} K_B aB bB i hAmpB
      exact ⟨J, hJa, hJb, hJinj, ⟨(D.functor.commShiftIso i).app K ≪≫ eJ⟩⟩
    have hHomB : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{w,
        max v u w, max v u w + 1} B).hom.obj
          (Opposite.op Q_B, Y_B)).IsLE (bB - i) := by
      simpa using derivedHom_isLE_of_injectiveAmplitude.{w, max v u w}
        Q_B Y_B (0 : ℤ) (aB - i) (bB - i) hQgeB hAmpYB
    have hHomA : ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u,
        max v u w, max v u w + 1} A).obj
          (Opposite.op Q_A, Y_A)).IsLE (bB - i) :=
      derivedHom_isLE_reflects f hf Q_A Y_A (bB - i) hBC hHomB
    have hHomA' : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u,
        max v u w, max v u w + 1} A).hom.obj
          (Opposite.op Q_A, Y_A)).IsLE (bB - i) :=
      hHomA
    have hExt := hom_ext_subsingleton_of_derivedHom_isLE.{u, max v u w} Q_A Y_A (aB - i)
      (bB - i) hYgeA hHomA' (by omega)
    change Subsingleton (DerivedCategory.Ext Q_A K i)
    exact hExt
  exact ⟨hFID, hcohA, homothetyQuasiIso_of_faithfullyFlat f hf K
    (pseudoCoherent_of_bounded_finite_cohomology.{u, max v w} K bB hcohA hLE_A) hK⟩

end Dualizing

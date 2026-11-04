module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Cohomology after a flat change of both algebras

Let `R → R'` be a homomorphism of commutative rings, let `A` and `B` be `R`-algebras, let `A'`
and `B'` be `R'`-algebras, and let `A → A'` and `B → B'` be homomorphisms of `R`-algebras
compatible with `R → R'`. Write `C = A ⊗[R] B` and `C' = A' ⊗[R'] B'`.

Under the flatness hypotheses of the Tor-independence criterion — `R'` flat over `R`, `A'` flat
over `A ⊗[R] R'` and `B'` flat over `R' ⊗[R] B` — the composite of the two derived base changes
`D(A) ⥤ D(A') ⥤ D(C')` and the single derived base change `D(A) ⥤ D(C)` followed by extension of
scalars along `C → C'` have naturally isomorphic cohomology in every degree.

## Main definitions

There are no new definitions.

## Main results

* `RingTheory.TorIndependence.derivedBaseChangeHomologyIso_of_flat`: the canonical natural
  isomorphism between the two cohomology functors `D(A) ⥤ ModuleCat C'`.

## Implementation notes

The two `C`- and `C'`-module structures on the iterated derived tensor products are pinned down
by deriving extension of scalars along the canonical algebra maps `A → A ⊗[R] B` and
`A' → A' ⊗[R'] B'`. Derived extension of scalars composes: the total left derived functor of
`- ⊗_R S` followed by that of `- ⊗_S T` is the total left derived functor of `- ⊗_R T`, because
both sides are computed by the same K-flat complexes and base change preserves K-flatness. For a
flat ring map, extension of scalars is exact, so its derived functor is the degreewise functor
read on derived categories, which commutes with cohomology.

## References

* [The Stacks Project, Tag 0DJD](https://stacks.math.columbia.edu/tag/0DJD)
* [The Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.DerivedExtensionScalars CochainComplex.KFlat

/-- Degreewise extension of scalars along a composite agrees with the composite of the
degreewise extensions, after localization to the derived category. -/
private def extensionScalarsComplexCompIso
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      extensionOfScalarsComplex.{u, u, u} g ≅
        extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
      (.up ℤ)) DerivedCategory.Q

/-- The comparison from the composite of the two total derived extension-of-scalars functors to
degreewise extension of scalars along the composite ring map. -/
private def derivedExtensionCompComparison
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, u} g).functor) ⟶
        extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  whiskerRight (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).functor ≫
    whiskerLeft ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ))
      (totalDerivedExtensionScalars.{u, u, u} g).comparison ≫
    (extensionScalarsComplexCompIso f g).hom

/-- Derived extension of scalars is compatible with composition of ring maps: both composites
are total left derived functors of degreewise extension of scalars along the composite, since
K-flat complexes compute either one and base change carries K-flat complexes to K-flat
complexes. -/
private def derivedExtensionCompIso
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, u} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor := by
  let D := totalDerivedExtensionScalars.{u, u, u} (g.comp f)
  let α := D.functor.leftDerivedLift D.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) _
    (derivedExtensionCompComparison f g)
  have hα (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
      IsIso (α.app (DerivedCategory.Q.obj P)) := by
    have hD := D.comparison_isIso_of_kFlat P hP
    have hfP : IsIso ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) :=
      (totalDerivedExtensionScalars.{u, u, u} f).comparison_isIso_of_kFlat P hP
    have hgP : IsIso ((totalDerivedExtensionScalars.{u, u, u} g).comparison.app
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P)) :=
      (totalDerivedExtensionScalars.{u, u, u} g).comparison_isIso_of_kFlat _
        (kFlat_baseChange f P hP)
    have hfac := D.functor.leftDerived_fac_app D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) _
      (derivedExtensionCompComparison f g) P
    have : IsIso ((derivedExtensionCompComparison f g).app P) := by
      change IsIso ((totalDerivedExtensionScalars.{u, u, u} g).functor.map
        ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (extensionScalarsComplexCompIso f g).hom.app P)
      have hm : IsIso ((totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P)) := inferInstance
      have he : IsIso ((extensionScalarsComplexCompIso f g).hom.app P) := inferInstance
      exact IsIso.comp_isIso' hm (IsIso.comp_isIso' hgP he)
    exact (isIso_comp_right_iff (α.app (DerivedCategory.Q.obj P)) (D.comparison.app P)).mp
      (hfac ▸ this)
  have (X : DerivedCategory (ModuleCat.{u} R)) : IsIso (α.app X) := by
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage X)
    have := hp
    have := hα P hP
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    have : IsIso (α.app (DerivedCategory.Q.obj P) ≫ D.functor.map e.hom) := inferInstance
    rw [← α.naturality] at this
    exact (isIso_comp_left_iff _ _).mp this
  exact @asIso _ _ _ _ α (NatIso.isIso_of_isIso_app α)

/-- For a flat ring map, extension of scalars is exact, so its total left derived functor is the
degreewise functor read on derived categories. -/
private def flatDerivedExtensionIso
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    (totalDerivedExtensionScalars.{u, u, u} f).functor ≅
      (ModuleCat.extendScalars f).mapDerivedCategory := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let F := ModuleCat.extendScalars f
  let D := totalDerivedExtensionScalars.{u, u, u} f
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso D.functor F.mapDerivedCategory
    D.comparison F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)

/-- The induced map of tensor-product algebras `A ⊗[R] B → A' ⊗[R'] B'` is flat as soon as `R'`
is flat over `R`, `A'` is flat over `A ⊗[R] R'` and `B'` is flat over `R' ⊗[R] B`. It factors as
a base change of `A → A'`, an isomorphism, and a base change of `R' ⊗[R] B → B'`. -/
private theorem flat_tensorProductMap
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hR' : RingHom.Flat (algebraMap R R'))
    (hA' : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (hB' : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R R' B') fB (fun _ _ ↦ Commute.all _ _)).toRingHom) :
    (TorChangeOfRings.tensorProductMap R R' A B A' B' fA fB).Flat := by
  have hR : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hR'
  have hfA : fA.toRingHom.Flat := by
    have h : (algebraMap A (A ⊗[R] R')).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    convert h.comp hA' using 1
    ext a
    simp
  let b : (R' ⊗[R] B) →ₐ[R'] B' :=
    { __ := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' B') fB
        (fun _ _ ↦ Commute.all _ _)
      commutes' r := by simp }
  let e := Algebra.TensorProduct.cancelBaseChange R R' R' A' B
  have h₁ : (Algebra.TensorProduct.map fA (AlgHom.id R B)).Flat :=
    hfA.tensorProductMap (RingHom.Flat.id B)
  have h₂ : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have h₃ : (Algebra.TensorProduct.lTensor (S := R') A' b).Flat :=
    (show b.Flat from hB').lTensor (S := R') A'
  convert (h₁.comp h₂).comp h₃ using 1
  ext a <;> simp [TorChangeOfRings.tensorProductMap, e, b]

/-- **Stacks 0DJD.** Under the flatness hypotheses of Tag 08HW, the cohomology of
`(M ⊗ᴸ_A A') ⊗ᴸ_{R'} B'` is canonically and naturally isomorphic, as a module over
`A' ⊗[R'] B'`, to the extension of scalars of the cohomology of `M ⊗ᴸ_R B` along
`A ⊗[R] B → A' ⊗[R'] B'`. -/
@[stacks 0DJD, no_expose]
public def derivedBaseChangeHomologyIso_of_flat
    (R R' A B A' B' : Type u)
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    [Algebra R' A'] [Algebra R' B'] [IsScalarTower R R' A'] [IsScalarTower R R' B']
    (fA : A →ₐ[R] A') (fB : B →ₐ[R] B')
    (hR' : RingHom.Flat (algebraMap R R'))
    (hA' : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (hB' : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R R' B') fB (fun _ _ ↦ Commute.all _ _)).toRingHom)
    (i : ℤ) :
    let C := A ⊗[R] B
    let C' := A' ⊗[R'] B'
    let extAA' := (totalDerivedExtensionScalars.{u, u, u} fA.toRingHom).functor
    let extAC := (totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* C)).functor
    let extA'C' := (totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A' →+* C')).functor
    let g : C →+* C' :=
      TorChangeOfRings.tensorProductMap R R' A B A' B' fA fB
    extAA' ⋙ extA'C' ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} C') i ≅
      extAC ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} C) i ⋙
        ModuleCat.extendScalars g := by
  let C := A ⊗[R] B
  let C' := A' ⊗[R'] B'
  let c : A →+* C := Algebra.TensorProduct.includeLeftRingHom
  let k : A' →+* C' := Algebra.TensorProduct.includeLeftRingHom
  let g : C →+* C' := TorChangeOfRings.tensorProductMap R R' A B A' B' fA fB
  have hg : g.Flat := flat_tensorProductMap R R' A B A' B' fA fB hR' hA' hB'
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hg
  have hcomp : k.comp fA.toRingHom = g.comp c := by
    ext a
    change fA a ⊗ₜ[R'] (1 : B') =
      (Algebra.TensorProduct.lift
        ((Algebra.TensorProduct.includeLeft : A' →ₐ[R'] C').restrictScalars R |>.comp fA)
        ((Algebra.TensorProduct.includeRight : B' →ₐ[R'] C').restrictScalars R |>.comp fB)
        (fun _ _ ↦ Commute.all _ _)) (a ⊗ₜ[R] (1 : B))
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  let e : (totalDerivedExtensionScalars.{u, u, u} fA.toRingHom).functor ⋙
      (totalDerivedExtensionScalars.{u, u, u} k).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} c).functor ⋙
      (totalDerivedExtensionScalars.{u, u, u} g).functor :=
    derivedExtensionCompIso fA.toRingHom k ≪≫
      eqToIso (congrArg (fun h : A →+* C' ↦
        (totalDerivedExtensionScalars.{u, u, u} h).functor) hcomp) ≪≫
      (derivedExtensionCompIso c g).symm
  exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (isoWhiskerRight (flatDerivedExtensionIso g hg) _ ≪≫
      StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.extendScalars g) i)

end RingTheory.TorIndependence

end

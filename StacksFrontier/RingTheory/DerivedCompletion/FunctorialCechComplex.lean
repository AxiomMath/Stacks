module

public import StacksFrontier.RingTheory.LocalCohomology.CechModel
public import StacksFrontier.RingTheory.LocalCohomology.RestrictScalars
public import StacksFrontier.Algebra.Homology.KFlat

/-!
# A complex computing local cohomology, functorially in the ring

Let `A` be a commutative ring and `I ⊆ A` a finitely generated ideal. The extended alternating
Čech complex on a finite generating family of `I` computes `RΓ_{V(I)}(A)`, but it depends on the
chosen family, so it is not functorial in `A`. A *functorial Čech datum* is a choice, for every
pair `(A, I)`, of a complex `K(A, I)` of `A`-modules together with an augmentation
`K(A, I) → A` and, for every ring map `φ : A → B`, a map of complexes of `A`-modules
`K(A, I) → K(B, IB)`, such that the augmentations and the compositions are respected on the
nose, the induced map `K(A, I) ⊗^L_A B → K(B, IB)` is an isomorphism in `D(B)`, and `K(A, I)` is
identified in `D(A)` with the extended alternating Čech complex on any finite generating family
of `I`, compatibly with the augmentations.

This file states that notion and derives its basic consequences: a functorial Čech datum computes
local cohomology, its complexes have `I`-power-torsion cohomology, and it is unique up to
isomorphism in `D(A)` over `A`. The existence of a functorial Čech datum is not proved here.

## Main definitions

* `Stacks.LocalCohomology.derivedBaseChange` — the morphism `K ⊗^L_A B → L` of `D(B)` induced by
  a map of complexes `K → L` of `A`-modules, `L` being a complex of `B`-modules.
* `Stacks.LocalCohomology.FunctorialCechData` — the data and the properties of Stacks 099D.
* `Stacks.LocalCohomology.FunctorialCechData.derivedAugmentation` — the augmentation
  `K(A, I) → A`, as a morphism of `D(A)` onto `A` placed in degree zero.

## Main results

* `Stacks.LocalCohomology.FunctorialCechData.nonempty_localCohomology_iso` — for a functorial
  Čech datum, `K(A, I)` is isomorphic in `D(A)` to `RΓ_{V(I)}(A)`.
* `Stacks.LocalCohomology.FunctorialCechData.derivedPowerTorsionProperty_complex` — the cohomology
  of `K(A, I)` is `I`-power torsion.
* `Stacks.LocalCohomology.FunctorialCechData.nonempty_homology_localCohomology_iso` — the local
  cohomology modules `H^i_{V(I)}(A)` are the cohomology modules of `K(A, I)`.
* `Stacks.LocalCohomology.FunctorialCechData.exists_iso_over_self` — two functorial Čech data
  give isomorphic complexes in `D(A)`, by an isomorphism carrying one augmentation onto the other.

## Implementation notes

The three pieces of data are honest complexes and honest maps of complexes, as in the source:
the point of the statement is that the maps of (3) compose on the nose, which is strictly
stronger than commutativity in `D(A)` and is what makes `K` a functor on the category of pairs.
Conditions (c) and (d), on the other hand, are conditions in the derived category and are stated
there; in particular (d) asserts the existence of an isomorphism of `D(A)`, not of a
quasi-isomorphism of complexes, since the source's construction produces only the former.

The ideal `IB` is passed as a separate argument `J` together with the equation `J = Ideal.map φ I`
rather than being spelled out. This is the same data, and it lets the composition law (b) be
stated without transporting along `Ideal.map_map`.

All rings live in a single universe `u` and all module categories are `ModuleCat.{u}`: a
structure field cannot quantify over universes, so a datum whose rings range over `Type u` is
the universe-polymorphic form of the statement.

The derived categories are the standard models, enabled as a local instance; this is the
convention of `StacksFrontier/RingTheory/LocalCohomology/`.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

section Comparison

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A ring map `φ : A → B`, viewed as an `A`-linear map from `A` to `B`, the `A`-module structure
on `B` being the one obtained by restriction of scalars along `φ`. -/
def restrictedRingHom (φ : A →+* B) :
    ModuleCat.of A A ⟶ (ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of B B) :=
  ConcreteCategory.ofHom (C := ModuleCat.{u} A)
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun a x => φ.map_mul a x }

/-- A ring map `φ : A → B`, viewed as a map from `A` placed in degree zero to `B` placed in
degree zero, as complexes of `A`-modules. -/
def singleRingHom (φ : A →+* B) :
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      (CochainComplex.restrictScalars φ).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map (restrictedRingHom φ) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars.{u} φ) (ComplexShape.up ℤ) 0).inv.app (ModuleCat.of B B)

/-- Restriction of scalars along a composite of ring maps, on complexes, identified with the
composite of the two restrictions of scalars. -/
def restrictScalarsCompComplexIso (φ : A →+* B) (ψ : B →+* C) :
    CochainComplex.restrictScalars ψ ⋙ CochainComplex.restrictScalars φ ≅
      CochainComplex.restrictScalars (ψ.comp φ) :=
  Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp.{u} φ ψ).symm (ComplexShape.up ℤ)

/-- **The base-change comparison map.** A map `u : K → L` from a complex of `A`-modules to a
complex of `B`-modules, restricted to `A`, induces by adjunction a morphism
`K ⊗^L_A B → L` in `D(B)`. -/
def derivedBaseChange (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L) :
    (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj L :=
  ((derivedExtensionRestrictAdjunction.{u, u, u} φ).homEquiv _ _).symm
    (DerivedCategory.Q.map u ≫
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app L)

end Comparison

/-- **Stacks 099D, the data and the conditions.** A *functorial Čech datum* assigns to every
commutative ring `A` and finitely generated ideal `I ⊆ A` a complex `K(A, I)` of `A`-modules
with an augmentation onto `A`, and to every ring map `φ : A → B` a map of complexes of
`A`-modules `K(A, I) → K(B, IB)`, subject to the four conditions of the source: compatibility
with the augmentations, the composition law, invertibility of the base-change comparison in
`D(B)`, and identification with the extended alternating Čech complex on a finite generating
family. -/
structure FunctorialCechData where
  /-- (1) The complex `K(A, I)` of `A`-modules. -/
  complex (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    CochainComplex (ModuleCat.{u} A) ℤ
  /-- (2) The augmentation `K(A, I) → A`. -/
  augmentation (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    complex A I hI ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  /-- (3) For a ring map `φ : A → B` and `J = IB`, the map `K(A, I) → K(B, J)` of complexes of
  `A`-modules. -/
  map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hI : I.FG)
    (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) :
    complex A I hI ⟶ (CochainComplex.restrictScalars φ).obj (complex B J hJ)
  /-- (a) The map of (3) is compatible with the augmentations of (2). -/
  map_augmentation {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) :
    map φ I hI J hJ hφ ≫ (CochainComplex.restrictScalars φ).map (augmentation B J hJ) =
      augmentation A I hI ≫ singleRingHom φ
  /-- (b) The maps of (3) compose. -/
  map_map {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C)
    (I : Ideal A) (hI : I.FG) (J : Ideal B) (hJ : J.FG) (K : Ideal C) (hK : K.FG)
    (hφ : J = I.map φ) (hψ : K = J.map ψ) :
    map (ψ.comp φ) I hI K hK (by rw [hψ, hφ, Ideal.map_map]) =
      map φ I hI J hJ hφ ≫
        (CochainComplex.restrictScalars φ).map (map ψ J hJ K hK hψ) ≫
          (restrictScalarsCompComplexIso φ ψ).hom.app (complex C K hK)
  /-- (c) The induced map `K(A, I) ⊗^L_A B → K(B, IB)` is an isomorphism in `D(B)`. -/
  isIso_derivedBaseChange {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) :
    IsIso (derivedBaseChange φ (map φ I hI J hJ hφ))
  /-- (d) For `I = (f₁, …, f_r)` there is an isomorphism in `D(A)` from the extended alternating
  Čech complex on `f₁, …, f_r` to `K(A, I)`, over the identity of `A`. -/
  exists_cech_iso (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) :
    ∃ e : extendedCechObject f (ModuleCat.of A A) ≅
        DerivedCategory.Q.obj (complex A I hI),
      e.hom ≫ DerivedCategory.Q.map (augmentation A I hI) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
            (ModuleCat.of A A)).inv =
        extendedCechAugmentationHom f (ModuleCat.of A A)

namespace FunctorialCechData

variable (D : FunctorialCechData.{u}) (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- The augmentation of `K(A, I)`, as a morphism of `D(A)` onto `A` placed in degree zero. -/
def derivedAugmentation :
    DerivedCategory.Q.obj (D.complex A I hI) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
  DerivedCategory.Q.map (D.augmentation A I hI) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).inv

/-- Condition (d) for an arbitrary finitely generated ideal, keeping track of the generating
family. -/
private theorem exists_generating_family_cech_iso :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = I ∧
      ∃ e : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI),
        e.hom ≫ D.derivedAugmentation A I hI =
          extendedCechAugmentationHom f (ModuleCat.of A A) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  obtain ⟨e, he⟩ := D.exists_cech_iso A f I hI hf
  exact ⟨r, f, hf, e, he⟩

/-- Condition (d), stated for an arbitrary finitely generated ideal: there is a finite generating
family, and the extended Čech complex on it is isomorphic to `K(A, I)` in `D(A)` over `A`. -/
theorem exists_extendedCech_iso :
    ∃ (r : ℕ) (f : Fin r → A) (e : extendedCechObject f (ModuleCat.of A A) ≅
        DerivedCategory.Q.obj (D.complex A I hI)),
      e.hom ≫ D.derivedAugmentation A I hI = extendedCechAugmentationHom f (ModuleCat.of A A) := by
  obtain ⟨r, f, -, e, he⟩ := D.exists_generating_family_cech_iso A I hI
  exact ⟨r, f, e, he⟩

/-- **A functorial Čech datum computes local cohomology.** The complex `K(A, I)` is isomorphic in
`D(A)` to `RΓ_{V(I)}(A)`. -/
theorem nonempty_localCohomology_iso :
    Nonempty ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≅
      DerivedCategory.Q.obj (D.complex A I hI)) := by
  obtain ⟨r, f, hf, e, -⟩ := D.exists_generating_family_cech_iso A I hI
  obtain ⟨c⟩ := nonempty_localCohomology_iso_extendedCechObject f (ModuleCat.of A A) I hI hf
  exact ⟨c.trans e⟩

/-- **The cohomology of `K(A, I)` is `I`-power torsion**, so `K(A, I)` is an object of
`D_{I^∞-torsion}(A)`. -/
theorem derivedPowerTorsionProperty_complex :
    Dualizing.derivedPowerTorsionProperty A I hI (DerivedCategory.Q.obj (D.complex A I hI)) := by
  obtain ⟨r, f, hf, e, -⟩ := D.exists_generating_family_cech_iso A I hI
  intro i m
  set c := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e with hc
  obtain ⟨n, hn, hkill⟩ :=
    derivedPowerTorsionProperty_extendedCechObject f (ModuleCat.of A A) I hI hf i (c.inv m)
  refine ⟨n, hn, fun a ha => ?_⟩
  have h : c.hom (a • c.inv m) = a • m := by
    rw [map_smul, ← ModuleCat.comp_apply, c.inv_hom_id, ModuleCat.id_apply]
  rw [← h, hkill a ha, map_zero]

/-- **The local cohomology modules of `A` are the cohomology modules of `K(A, I)`.** -/
theorem nonempty_homology_localCohomology_iso (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))) ≅
      (D.complex A I hI).homology i) := by
  obtain ⟨e⟩ := D.nonempty_localCohomology_iso A I hI
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app (D.complex A I hI)⟩

/-- **A functorial Čech datum is unique up to isomorphism over `A`.** Any two functorial Čech
data give complexes isomorphic in `D(A)`, by an isomorphism carrying one augmentation onto the
other. -/
theorem exists_iso_over_self (D' : FunctorialCechData.{u}) :
    ∃ e : DerivedCategory.Q.obj (D.complex A I hI) ≅
        DerivedCategory.Q.obj (D'.complex A I hI),
      e.hom ≫ D'.derivedAugmentation A I hI = D.derivedAugmentation A I hI := by
  obtain ⟨r, f, hf, e, he⟩ := D.exists_generating_family_cech_iso A I hI
  obtain ⟨e', he'⟩ := D'.exists_cech_iso A f I hI hf
  refine ⟨e.symm.trans e', ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, show e'.hom ≫ D'.derivedAugmentation A I hI = _
    from he', ← he, Iso.inv_hom_id_assoc]

end FunctorialCechData

end Stacks.LocalCohomology

end

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.Splitting
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.StrictlyHenselianFromRetractions
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtensionWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitBijection
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# W-local ind-étale extensions of a map with algebraic residue extensions

A map of rings `A → B` which induces algebraic extensions on residue fields fits into a
commutative square

```
B ──→ D
↑     ↑
A ──→ C
```

whose horizontal maps are faithfully flat and ind-étale. The spectra of `C` and of `D` are
w-local, the map `Spec D → Spec C` is w-local, the closed points of `Spec D` are the inverse
image of the closed points of `Spec C`, the closed points of `Spec C` and of `Spec D` surject
onto `Spec A` and `Spec B`, and the local rings of `C` at its maximal ideals are strictly
henselian.

## Main results

* `AlgebraicGeometry.ProEtale.exists_wLocal_faithfullyFlat_indEtale_extensions`: a ring map
  inducing algebraic extensions on residue fields fits into a commutative square as above.

## References

* [Stacks Project, Tag 097X](https://stacks.math.columbia.edu/tag/097X)
-/

open CategoryTheory TopologicalSpace
open scoped TensorProduct

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- Residue-field maps agree as soon as the underlying local homomorphisms do; the two
local-homomorphism witnesses are irrelevant. -/
private theorem residueField_map_congr {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f f' : R →+* S) (hf : IsLocalHom f) (hf' : IsLocalHom f') (h : f = f') :
    @IsLocalRing.ResidueField.map R S _ _ _ _ f hf =
      @IsLocalRing.ResidueField.map R S _ _ _ _ f' hf' := by
  subst h
  rfl

/-- The residue-field map of `Spec` of a ring map agrees, under the canonical identification of
the residue field of a point of `Spec R` with the residue field of the corresponding prime,
with the map induced on residue fields by that ring map. -/
private theorem spec_residueFieldMap_eq_ideal_residueFieldMap
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    (q : PrimeSpectrum B) :
    (Scheme.Spec.residueFieldIso (.of A)
        (PrimeSpectrum.comap g q)).hom ≫
    CommRingCat.ofHom (Ideal.ResidueField.map (q.asIdeal.comap g) q.asIdeal g rfl) =
      (Scheme.Spec.map (CommRingCat.ofHom g).op).residueFieldMap q ≫
        (Scheme.Spec.residueFieldIso (.of B) q).hom := by
  apply CommRingCat.hom_ext
  have hstalk := Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom g) q
  have hloc := congrArg (fun h => h ≫ (Spec.stalkIso (.of B) q).hom) hstalk
  simp only [Category.assoc, Iso.inv_hom_id] at hloc
  have hloc' :
      (Localization.localRingHom (PrimeSpectrum.comap g q).asIdeal q.asIdeal g rfl).comp
          (Spec.stalkIso (.of A) (PrimeSpectrum.comap g q)).hom.hom =
        (Spec.stalkIso (.of B) q).hom.hom.comp
          ((Scheme.Spec.map (CommRingCat.ofHom g).op).stalkMap q).hom :=
    CommRingCat.hom_ext_iff.mp hloc
  let : IsLocalHom (Spec.stalkIso (.of A) (PrimeSpectrum.comap g q)).hom.hom :=
    isLocalHom_of_isIso _
  let : IsLocalHom (Spec.stalkIso (.of B) q).hom.hom := isLocalHom_of_isIso _
  let : IsLocalHom ((Scheme.Spec.map (CommRingCat.ofHom g).op).stalkMap q).hom :=
    (Scheme.Spec.map (CommRingCat.ofHom g).op).prop q
  let : IsLocalHom ((Spec.stalkIso (.of B) q).hom.hom.comp
      ((Scheme.Spec.map (CommRingCat.ofHom g).op).stalkMap q).hom) :=
    RingHom.isLocalHom_comp _ _
  let : (PrimeSpectrum.comap g q).asIdeal.IsPrime := (PrimeSpectrum.comap g q).isPrime
  let : q.asIdeal.IsPrime := q.isPrime
  let : IsLocalHom (Localization.localRingHom (PrimeSpectrum.comap g q).asIdeal q.asIdeal
      g rfl) :=
    Localization.isLocalHom_localRingHom _ q.asIdeal g rfl
  let : IsLocalHom ((Localization.localRingHom (PrimeSpectrum.comap g q).asIdeal q.asIdeal
      g rfl).comp (Spec.stalkIso (.of A) (PrimeSpectrum.comap g q)).hom.hom) :=
    RingHom.isLocalHom_comp _ _
  let : IsLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk (PrimeSpectrum.comap g q)) :=
    (Spec (CommRingCat.of A)).toLocallyRingedSpace.isLocalRing _
  let : IsLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk q) :=
    (Spec (CommRingCat.of B)).toLocallyRingedSpace.isLocalRing _
  change (Ideal.ResidueField.map (PrimeSpectrum.comap g q).asIdeal q.asIdeal g rfl).comp
      (IsLocalRing.ResidueField.map (Spec.stalkIso (.of A)
        (PrimeSpectrum.comap g q)).hom.hom) =
    (IsLocalRing.ResidueField.map (Spec.stalkIso (.of B) q).hom.hom).comp
      (IsLocalRing.ResidueField.map
        ((Scheme.Spec.map (CommRingCat.ofHom g).op).stalkMap q).hom)
  rw [← IsLocalRing.ResidueField.map_comp, ← IsLocalRing.ResidueField.map_comp]
  exact residueField_map_congr _ _ _ _ hloc'

/-- Algebraicity of the residue-field extensions of `Spec B → Spec A` reads on ideals: for each
prime `q` of `B`, the residue field of `q` is algebraic over the residue field of its
contraction. -/
private theorem algebraic_ideal_residueFieldMap_of_scheme_residueFieldMap
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hres : let f : AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
      ∀ x,
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsAlgebraic
          ((AlgebraicGeometry.Spec (.of A)).residueField (f x))
          ((AlgebraicGeometry.Spec (.of B)).residueField x))
    (q : PrimeSpectrum B) :
    letI := (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap A B)) q.asIdeal
      (algebraMap A B) rfl).toAlgebra
    Algebra.IsAlgebraic (q.asIdeal.comap (algebraMap A B)).ResidueField q.asIdeal.ResidueField := by
  let p := PrimeSpectrum.comap (algebraMap A B) q
  let f : AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let := (f.residueFieldMap q).hom.toAlgebra
  have hscheme : Algebra.IsAlgebraic
      ((AlgebraicGeometry.Spec (.of A)).residueField (f q))
      ((AlgebraicGeometry.Spec (.of B)).residueField q) := hres q
  let eA : ((AlgebraicGeometry.Spec (.of A)).residueField (f q)) ≃+*
      (q.asIdeal.comap (algebraMap A B)).ResidueField :=
    (Scheme.Spec.residueFieldIso (.of A) p).commRingCatIsoToRingEquiv
  let eB : ((AlgebraicGeometry.Spec (.of B)).residueField q) ≃+* q.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv
  let ψ : (q.asIdeal.comap (algebraMap A B)).ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map (q.asIdeal.comap (algebraMap A B)) q.asIdeal
      (algebraMap A B) rfl
  let φ : ((AlgebraicGeometry.Spec (.of A)).residueField (f q)) →+*
      (AlgebraicGeometry.Spec (.of B)).residueField q := (f.residueFieldMap q).hom
  have hcomm : ψ.comp eA.toRingHom = eB.toRingHom.comp φ :=
    CommRingCat.hom_ext_iff.mp
      (spec_residueFieldMap_eq_ideal_residueFieldMap (algebraMap A B) q)
  have hbase : φ.comp eA.symm.toRingHom = eB.symm.toRingHom.comp ψ := RingHom.ext fun y ↦ by
    simpa using (congrArg eB.symm (congrArg (fun k => k (eA.symm y)) hcomm)).symm
  let : Algebra (q.asIdeal.comap (algebraMap A B)).ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap A B)) q.asIdeal
      (algebraMap A B) rfl).toAlgebra
  rw [Algebra.isAlgebraic_def]
  intro y
  have hy : IsAlgebraic ((AlgebraicGeometry.Spec (.of A)).residueField (f q))
      (eB.symm y) := hscheme.isAlgebraic (eB.symm y)
  exact hy.of_ringHom_of_comp_eq eA.symm.toRingHom eB.symm.toRingHom
    eA.symm.surjective eB.symm.injective hbase

/-- Ind-étaleness of `A → B` as a property of the object of `Under (CommRingCat.of A)` implies
that of `B` as an object of `CommAlgCat A`. -/
private theorem ind_etale_commAlgCat_of_indUnder (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (h : ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B) := by
  apply (CommAlgCat.ind_etale_iff_ind_algebraMap).2
  exact (MorphismProperty.ind_iff_ind_underMk
    (P := CommRingCat.etale.{u})
    (f := CommRingCat.ofHom (algebraMap A B))).2 h

/-- Ind-étaleness of `B` as an object of `CommAlgCat A` implies that of `A → B` as an object of
`Under (CommRingCat.of A)`. -/
private theorem indUnder_of_ind_etale_commAlgCat (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (h : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B)) :
    ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) := by
  change ObjectProperty.ind.{u} (MorphismProperty.underObj CommRingCat.etale)
    (Under.mk (CommRingCat.ofHom (algebraMap A B)))
  rwa [← MorphismProperty.ind_iff_ind_underMk, ← CommAlgCat.ind_etale_iff_ind_algebraMap]

/-- An ind-étale algebra is weakly étale. -/
private theorem weaklyEtale_of_indEtaleUnder
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    Algebra.WeaklyEtale A B := by
  rcases ind_etale_commAlgCat_of_indUnder A B h with ⟨J, _, _, pres, hstage⟩
  exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} A).2.2
    J pres.diag pres.cocone pres.isColimit (fun j ↦ by
      let : Algebra.Etale A (pres.diag.obj j) := hstage j
      infer_instance)

/-- An ind-étale algebra induces algebraic extensions of residue fields. -/
private theorem algebraic_residueField_of_indEtaleUnder
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))))
    (q : Ideal B) [q.IsPrime] :
    letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q
      (algebraMap A B) rfl).toAlgebra
    Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField := by
  let hweak := weaklyEtale_of_indEtaleUnder A B h
  let : Algebra.WeaklyEtale A B := hweak
  exact (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hweak
    (q.comap (algebraMap A B)) q rfl).2

/-- In a commutative square of algebras, algebraicity of the residue extensions along the two
sides through `B` forces algebraicity of the residue extension along `C → D`. -/
private theorem algebraic_residueField_of_algebraic_residueField_tower
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    (q : Ideal D) [q.IsPrime]
    (hAB : let pB := q.comap (algebraMap B D)
      let pA := pB.comap (algebraMap A B)
      letI : pB.IsPrime := Ideal.comap_isPrime _ _
      letI : pA.IsPrime := Ideal.comap_isPrime _ _
      letI := (Ideal.ResidueField.map pA pB (algebraMap A B) rfl).toAlgebra
      Algebra.IsAlgebraic pA.ResidueField pB.ResidueField)
    (hBD : let pB := q.comap (algebraMap B D)
      letI : pB.IsPrime := Ideal.comap_isPrime _ _
      letI := (Ideal.ResidueField.map pB q (algebraMap B D) rfl).toAlgebra
      Algebra.IsAlgebraic pB.ResidueField q.ResidueField) :
    let pC := q.comap (algebraMap C D)
    letI : pC.IsPrime := Ideal.comap_isPrime _ _
    letI := (Ideal.ResidueField.map pC q (algebraMap C D) rfl).toAlgebra
    Algebra.IsAlgebraic pC.ResidueField q.ResidueField := by
  let pB : Ideal B := q.comap (algebraMap B D)
  let pC : Ideal C := q.comap (algebraMap C D)
  let pA : Ideal A := pB.comap (algebraMap A B)
  let : pB.IsPrime := Ideal.comap_isPrime _ _
  let : pC.IsPrime := Ideal.comap_isPrime _ _
  let : pA.IsPrime := Ideal.comap_isPrime _ _
  have hAC : pA = pC.comap (algebraMap A C) := by
    dsimp [pA, pB, pC]
    change q.comap ((algebraMap B D).comp (algebraMap A B)) =
      q.comap ((algebraMap C D).comp (algebraMap A C))
    congr 1
    ext a
    simp [← IsScalarTower.algebraMap_apply A B D,
      ← IsScalarTower.algebraMap_apply A C D]
  let : Algebra pA.ResidueField pB.ResidueField :=
    (Ideal.ResidueField.map pA pB (algebraMap A B) rfl).toAlgebra
  let : Algebra pB.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map pB q (algebraMap B D) rfl).toAlgebra
  let : Algebra pA.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map pA q (algebraMap A D) (by
      dsimp [pA, pB]
      change q.comap ((algebraMap B D).comp (algebraMap A B)) = q.comap (algebraMap A D)
      congr 1
      ext a
      simp [← IsScalarTower.algebraMap_apply A B D])).toAlgebra
  let : Algebra pA.ResidueField pC.ResidueField :=
    (Ideal.ResidueField.map pA pC (algebraMap A C) hAC).toAlgebra
  let : Algebra pC.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map pC q (algebraMap C D) rfl).toAlgebra
  let : IsScalarTower A B pB.ResidueField := inferInstance
  let : IsScalarTower A C pC.ResidueField := inferInstance
  let : IsScalarTower A D q.ResidueField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A pB.ResidueField q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply A D q.ResidueField a,
      IsScalarTower.algebraMap_apply A B pB.ResidueField a]
    simp only [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply A B D a]
  let : IsScalarTower A pC.ResidueField q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply A D q.ResidueField a,
      IsScalarTower.algebraMap_apply A C pC.ResidueField a]
    simp only [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply A C D a]
  let : IsScalarTower pA.ResidueField pB.ResidueField q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply Ideal.ResidueField.ringHom_ext
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra,
      Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap D q.ResidueField)
      (IsScalarTower.algebraMap_apply A B D a)
  let : IsScalarTower pA.ResidueField pC.ResidueField q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply Ideal.ResidueField.ringHom_ext
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra,
      Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap D q.ResidueField)
      (IsScalarTower.algebraMap_apply A C D a)
  let : Algebra.IsAlgebraic pA.ResidueField pB.ResidueField := hAB
  let : Algebra.IsAlgebraic pB.ResidueField q.ResidueField := hBD
  have hAD : Algebra.IsAlgebraic pA.ResidueField q.ResidueField :=
    Algebra.IsAlgebraic.trans pA.ResidueField pB.ResidueField q.ResidueField
  let : Algebra.IsAlgebraic pA.ResidueField q.ResidueField := hAD
  exact Algebra.IsAlgebraic.extendScalars
    (RingHom.injective (Ideal.ResidueField.map pA pC (algebraMap A C) hAC))

/-- An ind-Zariski algebra is ind-étale. -/
private theorem indZariski_under_to_indEtale
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : IsIndZariski.{u, u, u} A B) :
    ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) := by
  let P : ObjectProperty (CommAlgCat.{u} A) := fun E ↦ Algebra.IsLocalIso A E
  let i : CommAlgCat.of A (ULift.{u} B) ≅ CommAlgCat.of A B :=
    CommAlgCat.isoMk (ULift.algEquiv (R := A))
  have h' : ObjectProperty.ind.{u} P (CommAlgCat.of A B) :=
    ObjectProperty.prop_of_iso (ObjectProperty.ind.{u} P) i h
  have hetale : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B) := by
    change ObjectProperty.ind.{u}
      (fun E : CommAlgCat.{u} A ↦ Algebra.IsLocalIso A E) (CommAlgCat.of A B) at h'
    rcases h' with ⟨J, hJ, hJf, pres, hstage⟩
    refine ⟨J, hJ, hJf, pres, fun j ↦ ?_⟩
    let := hstage j
    infer_instance
  exact indUnder_of_ind_etale_commAlgCat A B hetale

/-- `Scheme.Spec.map` of a ring map `f` sends the point of `Spec S` given by a prime `p` to the
point given by `PrimeSpectrum.comap f p`. -/
private theorem schemeSpecMap_specPointEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum S) :
    (Scheme.Spec.map (CommRingCat.ofHom f).op) (specPointEquiv S p) =
      specPointEquiv R (PrimeSpectrum.comap f p) := by
  apply (specPointEquiv R).injective
  rfl

/-- The closed points of the spectrum of the stratification colimit of `A` surject onto
`Spec A`. -/
private theorem stratification_closedPoints_surjective (A : Type u) [CommRing A] :
    ∀ x : PrimeSpectrum A,
      ∃ y : PrimeSpectrum (stratificationColimitRing (A := A)),
      y ∈ closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) ∧
      PrimeSpectrum.comap (stratificationColimitAlgebraMap (A := A)) y = x := by
  intro x
  let L := stratificationLimit (A := A)
  let A' := stratificationColimitRing (A := A)
  let eA := specPointEquiv A
  let eA' := specPointEquiv A'
  obtain ⟨z, hz⟩ :=
    (stratificationLimit_closedScheme_bijective (A := A) L).2 (eA x)
  let y : PrimeSpectrum A' := eA'.symm (L.inclusion.base z)
  refine ⟨y, ?_, ?_⟩
  · change IsClosed ({eA' y} : Set (stratificationLimitScheme (A := A)))
    have hy : L.inclusion.base z ∈ closedPoints (stratificationLimitScheme (A := A)) := by
      rw [← range_inclusion_eq_closedPoints L]
      exact ⟨z, rfl⟩
    simpa [y, eA'] using hy
  · apply eA.injective
    calc
      eA (PrimeSpectrum.comap (stratificationColimitAlgebraMap (A := A)) y) =
          Spec.map (CommRingCat.ofHom
            (stratificationColimitAlgebraMap (A := A))) (eA' y) :=
              (specMap_specPointEquiv _ _).symm
      _ = eA x := by
        simpa [y, eA', Scheme.Hom.comp_apply] using hz

/-- A prime containing an ideal is the contraction of a prime of the quotient. -/
private theorem primeSpectrum_quotient_lift
    {R : Type u} [CommRing R] (I : Ideal R) (q : PrimeSpectrum R)
    (hIq : I ≤ q.asIdeal) :
    ∃ qbar : PrimeSpectrum (R ⧸ I),
      PrimeSpectrum.comap (Ideal.Quotient.mk I) qbar = q := by
  let qbar : PrimeSpectrum (R ⧸ I) :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact hIq)⟩
  refine ⟨qbar, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk I)
    (Ideal.map (Ideal.Quotient.mk I) q.asIdeal) = q.asIdeal
  rw [Ideal.comap_map_of_surjective (f := Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective]
  apply sup_eq_left.mpr
  rwa [show Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (R ⧸ I)) =
    RingHom.ker (Ideal.Quotient.mk I) from rfl, Ideal.mk_ker]

/-- If a ring map becomes bijective on the quotients by an ideal and its extension, then every
prime containing the ideal is the contraction of a prime containing the extended ideal. -/
private theorem prime_lift_of_quotient_bijective
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (I : Ideal R)
    (q : PrimeSpectrum R) (hqI : I ≤ q.asIdeal)
    (hquot : Function.Bijective
      (Ideal.quotientMap (Ideal.map g I) g Ideal.le_comap_map :
        (R ⧸ I) →+* (S ⧸ Ideal.map g I))) :
    ∃ r : PrimeSpectrum S, Ideal.map g I ≤ r.asIdeal ∧ PrimeSpectrum.comap g r = q := by
  let J : Ideal S := Ideal.map g I
  let f : R ⧸ I →+* S ⧸ J :=
    Ideal.quotientMap J g Ideal.le_comap_map
  let e : (R ⧸ I) ≃+* (S ⧸ J) := RingEquiv.ofBijective f hquot
  obtain ⟨qbar, hqbar⟩ := primeSpectrum_quotient_lift I q hqI
  let rbar : PrimeSpectrum (S ⧸ J) := (PrimeSpectrum.comapEquiv e) qbar
  let r : PrimeSpectrum S := PrimeSpectrum.comap (Ideal.Quotient.mk J) rbar
  have hbar : PrimeSpectrum.comap f rbar = qbar := by
    apply PrimeSpectrum.ext
    change Ideal.comap f (Ideal.comap e.symm.toRingHom qbar.asIdeal) = qbar.asIdeal
    rw [Ideal.comap_comap]
    have heq : e.symm.toRingHom.comp f = RingHom.id _ := by
      ext x
      apply e.injective
      simp [e, f, Ideal.quotientMap_mk]
    rw [heq]
    simp
  have hcomp : (Ideal.Quotient.mk J).comp g = f.comp (Ideal.Quotient.mk I) := by
    ext x
    simp [f, J, Ideal.quotientMap_mk]
  have hcontract : PrimeSpectrum.comap g r = q := by
    rw [← PrimeSpectrum.comap_comp_apply g (Ideal.Quotient.mk J) rbar,
      hcomp, PrimeSpectrum.comap_comp_apply, hbar, hqbar]
  refine ⟨r, ?_, hcontract⟩
  change J ≤ Ideal.comap (Ideal.Quotient.mk J) rbar.asIdeal
  intro x hx
  change Ideal.Quotient.mk J x ∈ rbar.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact rbar.asIdeal.zero_mem

/-- A prime containing the extension of an ideal contracts to a prime containing that
ideal. -/
private theorem prime_preimage_of_le_map
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (I : Ideal R)
    (m : PrimeSpectrum S) (hmJ : Ideal.map g I ≤ m.asIdeal) :
    ∃ q : PrimeSpectrum R, I ≤ q.asIdeal ∧ PrimeSpectrum.comap g m = q :=
  ⟨PrimeSpectrum.comap g m, Ideal.map_le_iff_le_comap.mp hmJ, rfl⟩

/-- The composition of a flat ring map with an ind-Zariski one is flat. -/
private theorem flat_comp_indZariski
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra B C]
    (f : A →+* B) (hf : f.Flat)
    (hg : IsIndZariski.{u, u, u} B C) :
    ((algebraMap B C).comp f).Flat := by
  apply RingHom.Flat.ofLocalizationPrime
  intro q hq
  let : q.IsPrime := hq
  let p : Ideal B := q.comap (algebraMap B C)
  let r : Ideal A := q.comap ((algebraMap B C).comp f)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  let : r.IsPrime := Ideal.comap_isPrime _ _
  have hr : r = p.comap f := by
    dsimp [r, p]
    exact Ideal.comap_comap f (algebraMap B C)
  have hfp : (Localization.localRingHom r p f hr).Flat :=
    RingHom.Flat.localRingHom hf p r hr
  have hgp : (Localization.localRingHom p q (algebraMap B C) rfl).Flat :=
    RingHom.Flat.of_bijective (identifiesLocalRings_of_isIndZariski B C hg q)
  rw [Localization.localRingHom_comp r p q f hr (algebraMap B C) rfl]
  exact hfp.comp hgp

/-- The canonical algebra map between quotients by an ideal and its extension is the ring map
induced on quotients by the structure map. -/
private theorem algebraMap_quotient_eq_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) :
    (algebraMap (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) =
      Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map :=
  rfl

/-- Localizations at two equal primes are canonically isomorphic as algebras. -/
private noncomputable def localizationAtPrimeAlgEquivOfEq
    {S : Type u} [CommRing S] {r q : Ideal S} [r.IsPrime] [q.IsPrime] (h : r = q) :
    Localization.AtPrime r ≃ₐ[S] Localization.AtPrime q := by
  have hM : r.primeCompl = q.primeCompl := by subst h; rfl
  have hloc : IsLocalization q.primeCompl (Localization.AtPrime r) := by
    rw [← hM]
    infer_instance
  exact IsLocalization.algEquiv q.primeCompl _ _

/-- For every ring `A` there is a faithfully flat ind-étale `A`-algebra `C` whose spectrum is
w-local, whose closed points surject onto `Spec A`, and whose local rings at maximal ideals are
strictly henselian. -/
private theorem exists_initial_extension (A : Type u) [CommRing A] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      (algebraMap A C).FaithfullyFlat ∧
      ObjectProperty.ind.{u}
        (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
        (Under.mk (CommRingCat.ofHom (algebraMap A C))) ∧
      WLocalSpace (PrimeSpectrum C) ∧
      (∀ x : PrimeSpectrum A, ∃ y : PrimeSpectrum C,
        y ∈ closedPoints (PrimeSpectrum C) ∧ PrimeSpectrum.comap (algebraMap A C) y = x) ∧
      ∀ (m : Ideal C) [m.IsMaximal],
        StrictlyHenselianLocalRing (Localization.AtPrime m) := by
  let A' := stratificationColimitRing (A := A)
  let f : A →+* A' := stratificationColimitAlgebraMap (A := A)
  let : CommRing A' := inferInstance
  let : Algebra A A' := f.toAlgebra
  have hfFlat : f.FaithfullyFlat := stratificationColimit_faithfullyFlat (A := A)
  have hfIndZ : IsIndZariski.{u, u, u} A A' := stratificationColimit_isIndZariski (A := A)
  have hfIndEt : ObjectProperty.ind
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom f)) :=
    indZariski_under_to_indEtale A A' hfIndZ
  let : WLocalSpace (PrimeSpectrum A') := by
    change WLocalSpace (stratificationLimitScheme (A := A))
    exact stratificationLimitScheme_wLocal (A := A)
  have hclosedA' : IsClosed (closedPoints (PrimeSpectrum A')) :=
    WLocalSpace.isClosed_closedPoints
  obtain ⟨I, hIclosed⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (closedPoints (PrimeSpectrum A'))).mp
      hclosedA'
  have hzero : PrimeSpectrum.zeroLocus (I : Set A') = closedPoints (PrimeSpectrum A') :=
    hIclosed.symm
  obtain ⟨C', hC', algA'C', hffA'C', hIndA'C', hsplit⟩ :=
    exists_faithfullyFlat_ind_etale_algebra_splitting_etale A'
  let : CommRing C' := hC'
  let : Algebra A' C' := algA'C'
  have hresA'C' : ∀ q : Ideal C', ∀ [q.IsPrime],
      let := (Ideal.ResidueField.map (q.comap (algebraMap A' C')) q
        (algebraMap A' C') rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap A' C')).ResidueField q.ResidueField :=
    fun q ↦ algebraic_residueField_of_indEtaleUnder A' C' hIndA'C' q
  obtain ⟨C, hC, algC'C, hIndA'C_Z, hquot', hWC, -, hclosedC⟩ :=
    exists_isIndZariski_wLocal_of_isAlgebraic_residueField (algebraMap A' C') I hzero hresA'C'
  let : CommRing C := hC
  let : Algebra C' C := algC'C
  let g : C' →+* C := algebraMap C' C
  let : Algebra A' C := ((algebraMap C' C).comp (algebraMap A' C')).toAlgebra
  let : IsScalarTower A' C' C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A C := ((algebraMap A' C).comp f).toAlgebra
  let : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let I' : Ideal C' := Ideal.map (algebraMap A' C') I
  let J : Ideal C := Ideal.map g I'
  have hquot : Function.Bijective
      (Ideal.quotientMap (Ideal.map g I') g Ideal.le_comap_map :
        (C' ⧸ I') →+* (C ⧸ Ideal.map g I')) := by
    rwa [← algebraMap_quotient_eq_quotientMap (R := C') (S := C) I']
  have hA'Cflat : (algebraMap A' C').Flat := RingHom.FaithfullyFlat.flat hffA'C'
  have hA'Cflat' : (algebraMap A' C).Flat :=
    flat_comp_indZariski (algebraMap A' C') hA'Cflat hIndA'C_Z
  have hACflat : (algebraMap A C).Flat := by
    rw [show algebraMap A C = (algebraMap A' C).comp f from rfl]
    exact (RingHom.FaithfullyFlat.flat hfFlat).comp hA'Cflat'
  have hclosedSurj : ∀ x : PrimeSpectrum A, ∃ y : PrimeSpectrum C,
      y ∈ closedPoints (PrimeSpectrum C) ∧ PrimeSpectrum.comap (algebraMap A C) y = x := by
    intro x
    obtain ⟨p, hpclosed, hpx⟩ := stratification_closedPoints_surjective A x
    let : Module.FaithfullyFlat A' C' := RingHom.faithfullyFlat_algebraMap_iff.mp hffA'C'
    have hspecSurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A' C')) :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A') (B := C')
    obtain ⟨q', hq'⟩ := hspecSurj p
    let : q'.asIdeal.IsPrime := q'.isPrime
    have hpI : I ≤ p.asIdeal :=
      show p ∈ PrimeSpectrum.zeroLocus (I : Set A') by rwa [hzero]
    have hI'q' : I' ≤ q'.asIdeal := by
      apply Ideal.map_le_iff_le_comap.mpr
      change I ≤ (PrimeSpectrum.comap (algebraMap A' C') q').asIdeal
      simpa [hq'] using hpI
    obtain ⟨y, hyJ, hyq'⟩ :=
      prime_lift_of_quotient_bijective g I' q' hI'q' hquot
    have hyclosed : y ∈ closedPoints (PrimeSpectrum C) := by
      rw [hclosedC]
      change PrimeSpectrum.comap ((algebraMap C' C).comp (algebraMap A' C')) y ∈
        closedPoints (PrimeSpectrum A')
      rwa [PrimeSpectrum.comap_comp_apply, hyq', hq']
    refine ⟨y, hyclosed, ?_⟩
    rw [show algebraMap A C = (algebraMap A' C).comp f from rfl,
      PrimeSpectrum.comap_comp_apply,
      show algebraMap A' C = g.comp (algebraMap A' C') from rfl,
      PrimeSpectrum.comap_comp_apply, hyq', hq', hpx]
  have hACff : (algebraMap A C).FaithfullyFlat :=
    ((faithfullyFlat_tfae00HQ (algebraMap A C) hACflat).out 1 3).mpr
      (by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hclosedSurj x
        exact ⟨y, hxy⟩)
  have hC'indEt : ObjectProperty.ind
      (fun E : Under (CommRingCat.of C') ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom g)) :=
    indZariski_under_to_indEtale C' C hIndA'C_Z
  have hA'indEt : ObjectProperty.ind
      (fun E : Under (CommRingCat.of A') ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A' C))) :=
    indUnder_of_ind_etale_commAlgCat A' C <| CommAlgCat.ind_etale_comp
      (ind_etale_commAlgCat_of_indUnder A' C' hIndA'C')
      (ind_etale_commAlgCat_of_indUnder C' C hC'indEt)
  have hACindEt : ObjectProperty.ind
      (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A C))) :=
    indUnder_of_ind_etale_commAlgCat A C <| CommAlgCat.ind_etale_comp
      (ind_etale_commAlgCat_of_indUnder A A' hfIndEt)
      (ind_etale_commAlgCat_of_indUnder A' C hA'indEt)
  have hCstrict : ∀ (m : Ideal C) [m.IsMaximal],
      StrictlyHenselianLocalRing (Localization.AtPrime m) := by
    intro m hm
    let mSpec : PrimeSpectrum C := ⟨m, hm.isPrime⟩
    have hmclosed : mSpec ∈ closedPoints (PrimeSpectrum C) :=
      mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal mSpec).mpr hm)
    have hpclosed : PrimeSpectrum.comap ((algebraMap C' C).comp (algebraMap A' C')) mSpec ∈
        closedPoints (PrimeSpectrum A') := by
      rwa [hclosedC] at hmclosed
    let p : PrimeSpectrum A' :=
      PrimeSpectrum.comap ((algebraMap C' C).comp (algebraMap A' C')) mSpec
    have hpI : I ≤ p.asIdeal :=
      show p ∈ PrimeSpectrum.zeroLocus (I : Set A') by rwa [hzero]
    have hJm : J ≤ m := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.map_le_iff_le_comap.mpr
      change I ≤ (PrimeSpectrum.comap (algebraMap A' C')
        (PrimeSpectrum.comap g mSpec)).asIdeal
      simpa [p, PrimeSpectrum.comap_comp_apply, Ideal.comap_comap] using hpI
    obtain ⟨q', hI'q', hq'm⟩ :=
      prime_preimage_of_le_map g I' mSpec hJm
    have hq'closed : q' ∈ closedPoints (PrimeSpectrum C') := by
      apply closedPoints_of_mem_zeroLocus_map (algebraMap A' C') I hzero hresA'C'
      exact hI'q'
    let : q'.asIdeal.IsPrime := q'.isPrime
    have hq'max : q'.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q').mp
        (mem_closedPoints_iff.mp hq'closed)
    let : q'.asIdeal.IsMaximal := hq'max
    let : m.IsMaximal := hm
    have hloc := identifiesLocalRings_of_isIndZariski C' C hIndA'C_Z m
    have hq'mIdeal : q'.asIdeal = m.comap g := by
      have h := congrArg PrimeSpectrum.asIdeal hq'm
      simpa using h.symm
    let eEq : Localization.AtPrime q'.asIdeal ≃+*
        Localization.AtPrime (m.comap g) :=
      (localizationAtPrimeAlgEquivOfEq hq'mIdeal).toRingEquiv
    let eLoc' : Localization.AtPrime (m.comap g) ≃+* Localization.AtPrime m :=
      RingEquiv.ofBijective (Localization.localRingHom (m.comap g) m g rfl) hloc
    let eLoc : Localization.AtPrime q'.asIdeal ≃+* Localization.AtPrime m :=
      eEq.trans eLoc'
    have hRetracts : ∀ (T : Type u) [CommRing T] [Algebra C' T]
        [Algebra.Etale C' T] [Module.FaithfullyFlat C' T], Nonempty (T →ₐ[C'] C') := by
      intro T _ _ _ _
      apply hsplit
      · exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
      · exact inferInstance
    let : StrictlyHenselianLocalRing (Localization.AtPrime q'.asIdeal) :=
      localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts
        C' hRetracts q'.asIdeal
    exact strictlyHenselianLocalRing_of_ringEquiv eLoc
  exact ⟨C, hC, inferInstance, hACff, hACindEt, hWC, hclosedSurj, hCstrict⟩

/-- A ring map inducing algebraic extensions on residue fields admits a commutative square of
faithfully flat ind-étale extensions with w-local spectra, compatible closed points, and strictly
henselian local rings at the closed points of the lower-right ring. -/
@[stacks 097X]
theorem exists_wLocal_faithfullyFlat_indEtale_extensions
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hres : let f : AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
      ∀ x,
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsAlgebraic
          ((AlgebraicGeometry.Spec (.of A)).residueField (f x))
          ((AlgebraicGeometry.Spec (.of B)).residueField x)) :
    ∃ (C D : Type u) (_ : CommRing C) (_ : CommRing D)
      (_ : Algebra A C) (_ : Algebra A D) (_ : Algebra B D) (_ : Algebra C D)
      (_ : IsScalarTower A B D) (_ : IsScalarTower A C D),
      (algebraMap A C).FaithfullyFlat ∧
      ObjectProperty.ind.{u}
        (fun E : Under (CommRingCat.of A) ↦ E.hom.hom.Etale)
        (Under.mk (CommRingCat.ofHom (algebraMap A C))) ∧
      (algebraMap B D).FaithfullyFlat ∧
      ObjectProperty.ind.{u}
        (fun E : Under (CommRingCat.of B) ↦ E.hom.hom.Etale)
        (Under.mk (CommRingCat.ofHom (algebraMap B D))) ∧
      WLocalSpace (PrimeSpectrum C) ∧
      WLocalSpace (PrimeSpectrum D) ∧
      IsWLocalMap (PrimeSpectrum.comap (algebraMap C D)) ∧
      closedPoints (PrimeSpectrum D) =
        (PrimeSpectrum.comap (algebraMap C D)) ⁻¹' closedPoints (PrimeSpectrum C) ∧
      (∀ x : PrimeSpectrum A, ∃ y : PrimeSpectrum C,
        y ∈ closedPoints (PrimeSpectrum C) ∧
          PrimeSpectrum.comap (algebraMap A C) y = x) ∧
      (∀ x : PrimeSpectrum B, ∃ y : PrimeSpectrum D,
        y ∈ closedPoints (PrimeSpectrum D) ∧
          PrimeSpectrum.comap (algebraMap B D) y = x) ∧
      ∀ (m : Ideal C) [m.IsMaximal],
        StrictlyHenselianLocalRing (Localization.AtPrime m) := by
  obtain ⟨C, hC, algAC, hACff, hACind, hWC, hclosedSurjA, hCstrict⟩ :=
    exists_initial_extension A
  let : CommRing C := hC
  let : Algebra A C := algAC
  have hresAB : ∀ q : Ideal B, ∀ [q.IsPrime],
      let := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q
        (algebraMap A B) rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField := by
    intro q hq
    exact algebraic_ideal_residueFieldMap_of_scheme_residueFieldMap A B hres ⟨q, hq⟩
  let D' := B ⊗[A] C
  let : CommRing D' := inferInstance
  let : Algebra A D' := inferInstance
  let : Algebra B D' := Algebra.TensorProduct.leftAlgebra
  let : Algebra C D' := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A B D' := inferInstance
  let : IsScalarTower A C D' := inferInstance
  have hBD'ind : (CommAlgCat.etale.{u} B).ind.{u} (CommAlgCat.of B D') :=
    CommAlgCat.ind_etale_of_isPushout A B C D' (ind_etale_commAlgCat_of_indUnder A C hACind)
  have hBD'indUnder := indUnder_of_ind_etale_commAlgCat B D' hBD'ind
  have hBD'ff : (algebraMap B D').FaithfullyFlat := by
    have hmodule : Module.FaithfullyFlat B D' := by
      let : Module.FaithfullyFlat A C := RingHom.faithfullyFlat_algebraMap_iff.mp hACff
      infer_instance
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr hmodule
  have hresBD' : ∀ q : Ideal D', ∀ [q.IsPrime],
      let := (Ideal.ResidueField.map (q.comap (algebraMap B D')) q
        (algebraMap B D') rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap B D')).ResidueField q.ResidueField := by
    intro q hq
    exact algebraic_residueField_of_indEtaleUnder B D' hBD'indUnder q
  have hresCD' : ∀ q : Ideal D', ∀ [q.IsPrime],
      let pC := q.comap (algebraMap C D')
      let : pC.IsPrime := Ideal.comap_isPrime _ _
      let := (Ideal.ResidueField.map pC q (algebraMap C D') rfl).toAlgebra
      Algebra.IsAlgebraic pC.ResidueField q.ResidueField := by
    intro q hq
    exact algebraic_residueField_of_algebraic_residueField_tower A B C D' q
      (hresAB (q.comap (algebraMap B D')))
      (hresBD' q)
  have hclosedC : IsClosed (closedPoints (PrimeSpectrum C)) :=
    WLocalSpace.isClosed_closedPoints
  obtain ⟨J, hJclosed⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (closedPoints (PrimeSpectrum C))).mp hclosedC
  have hzeroJ : PrimeSpectrum.zeroLocus (J : Set C) = closedPoints (PrimeSpectrum C) :=
    hJclosed.symm
  let P := D' ⧸ Ideal.map (algebraMap C D') J
  let K : Ideal D' := Ideal.map (algebraMap C D') J
  let : CommRing P := inferInstance
  let : Algebra B P := inferInstance
  let : Algebra A P := inferInstance
  let : IsScalarTower A B P := inferInstance
  let : CommRing (C ⧸ J) := Ideal.Quotient.commRing J
  let : CommSemiring (C ⧸ J) := (Ideal.Quotient.commRing J).toCommSemiring
  let : Algebra A (C ⧸ J) := inferInstance
  let : Algebra B B := inferInstance
  let : IsScalarTower A B B :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := B) fun _ ↦ rfl
  let eQuot : B ⊗[A] (C ⧸ J) ≃ₐ[B] P :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := A) (S := B) (T := C) (A := B) J
  let e : P ≃ₐ[B] B ⊗[A] (C ⧸ J) := eQuot.symm
  let : Algebra (C ⧸ J) (B ⊗[A] (C ⧸ J)) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A (C ⧸ J) (B ⊗[A] (C ⧸ J)) := inferInstance
  let : Algebra (C ⧸ J) P :=
    ((e.symm.toRingEquiv.toRingHom).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := C ⧸ J)).toRingHom).toAlgebra
  let : IsScalarTower A (C ⧸ J) P := IsScalarTower.of_algebraMap_eq fun a ↦ by
    apply e.injective
    calc
      e (algebraMap A P a) =
          e (algebraMap B P (algebraMap A B a)) := by
            rw [IsScalarTower.algebraMap_apply A B P a]
      _ = algebraMap B (B ⊗[A] (C ⧸ J)) (algebraMap A B a) := e.commutes _
      _ = algebraMap A (B ⊗[A] (C ⧸ J)) a := by
            rw [IsScalarTower.algebraMap_apply A B (B ⊗[A] (C ⧸ J)) a]
      _ = algebraMap (C ⧸ J) (B ⊗[A] (C ⧸ J)) (algebraMap A (C ⧸ J) a) :=
            IsScalarTower.algebraMap_apply A (C ⧸ J) (B ⊗[A] (C ⧸ J)) a
      _ = e (algebraMap (C ⧸ J) P (algebraMap A (C ⧸ J) a)) := by
            change algebraMap (C ⧸ J) (B ⊗[A] (C ⧸ J))
                (algebraMap A (C ⧸ J) a) =
              eQuot.symm (eQuot (Algebra.TensorProduct.includeRight
                (R := A) (A := B) (B := C ⧸ J)
                (algebraMap A (C ⧸ J) a)))
            rw [Algebra.TensorProduct.right_algebraMap_apply, eQuot.symm_apply_apply]
            rfl
  have hfCquot : AlgebraicGeometry.Surjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (C ⧸ J))).op) := by
    constructor
    intro x
    obtain ⟨y, hyclosed, hyx⟩ := hclosedSurjA x
    have hyJ : J ≤ y.asIdeal := by
      change y ∈ PrimeSpectrum.zeroLocus (J : Set C)
      rwa [hzeroJ]
    obtain ⟨z, hzy⟩ := primeSpectrum_quotient_lift J y hyJ
    refine ⟨specPointEquiv (C ⧸ J) z, ?_⟩
    rw [schemeSpecMap_specPointEquiv]
    change PrimeSpectrum.comap (algebraMap A (C ⧸ J)) z = x
    have hcomp : algebraMap A (C ⧸ J) =
        (Ideal.Quotient.mk J).comp (algebraMap A C) := by
      ext a
      simp
    rwa [hcomp, PrimeSpectrum.comap_comp_apply, hzy]
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A (C ⧸ J)))
      (CommRingCat.ofHom (algebraMap B P))
      (CommRingCat.ofHom (algebraMap (C ⧸ J) P)) := by
    convert isPushout_of_algEquiv_tensorProduct A B (C ⧸ J) P e using 1
  have hpb := AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (algebraMap A (C ⧸ J)))
    (CommRingCat.ofHom (algebraMap B P))
    (CommRingCat.ofHom (algebraMap (C ⧸ J) P)) hpush
  have hSpecBP : AlgebraicGeometry.Surjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap B P)).op) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hfCquot
  have hBPsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B P)) := by
    intro x
    obtain ⟨z, hz⟩ := hSpecBP.surj (specPointEquiv B x)
    let p := (specPointEquiv P).symm z
    refine ⟨p, ?_⟩
    apply (specPointEquiv B).injective
    calc
      specPointEquiv B (PrimeSpectrum.comap (algebraMap B P) p) =
          Scheme.Spec.map (CommRingCat.ofHom (algebraMap B P)).op
            (specPointEquiv P p) :=
              (schemeSpecMap_specPointEquiv (R := B) (S := P)
                (f := algebraMap B P) p).symm
      _ = Scheme.Spec.map (CommRingCat.ofHom (algebraMap B P)).op z := by simp [p]
      _ = specPointEquiv B x := hz
  obtain ⟨D, hD, algD'D, hD'indZ, hquotD', hWD, hWmap, hclosedD⟩ :=
    exists_isIndZariski_wLocal_of_isAlgebraic_residueField (algebraMap C D') J hzeroJ hresCD'
  let : CommRing D := hD
  let : Algebra D' D := algD'D
  let g : D' →+* D := algebraMap D' D
  let : Algebra B D := (g.comp (algebraMap B D')).toAlgebra
  let : Algebra C D := (g.comp (algebraMap C D')).toAlgebra
  let : Algebra A D := (g.comp (algebraMap A D')).toAlgebra
  let : IsScalarTower B D' D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower C D' D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change g (algebraMap A D' a) =
      g (algebraMap B D' (algebraMap A B a))
    rw [← IsScalarTower.algebraMap_apply A B D' a]
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change g (algebraMap A D' a) =
      g (algebraMap C D' (algebraMap A C a))
    rw [← IsScalarTower.algebraMap_apply A C D' a]
  have hquotD : Function.Bijective
      (Ideal.quotientMap (Ideal.map g K) g Ideal.le_comap_map :
        (D' ⧸ K) →+* (D ⧸ Ideal.map g K)) := by
    rwa [← algebraMap_quotient_eq_quotientMap (R := D') (S := D) K]
  have hclosedSurjB : ∀ x : PrimeSpectrum B, ∃ y : PrimeSpectrum D,
      y ∈ closedPoints (PrimeSpectrum D) ∧ PrimeSpectrum.comap (algebraMap B D) y = x := by
    intro x
    obtain ⟨z, hzx⟩ := hBPsurj x
    let q' : PrimeSpectrum D' := PrimeSpectrum.comap (Ideal.Quotient.mk K) z
    have hKq' : K ≤ q'.asIdeal := by
      intro r hr
      change Ideal.Quotient.mk K r ∈ z.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact z.asIdeal.zero_mem
    have hq'B : PrimeSpectrum.comap (algebraMap B D') q' = x := by
      have hcomp : algebraMap B P = (Ideal.Quotient.mk K).comp (algebraMap B D') := rfl
      change PrimeSpectrum.comap (algebraMap B D')
        (PrimeSpectrum.comap (Ideal.Quotient.mk K) z) = x
      rwa [← PrimeSpectrum.comap_comp_apply, ← hcomp]
    obtain ⟨y, hyK, hyq'⟩ :=
      prime_lift_of_quotient_bijective g K q' hKq' hquotD
    let qC : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C D') q'
    have hJqC : J ≤ qC.asIdeal := by
      apply Ideal.map_le_iff_le_comap.mp
      exact hKq'
    have hqCclosed : qC ∈ closedPoints (PrimeSpectrum C) := by
      have hqzero : qC ∈ PrimeSpectrum.zeroLocus (J : Set C) := hJqC
      rwa [hzeroJ] at hqzero
    have hyclosed : y ∈ closedPoints (PrimeSpectrum D) := by
      rw [hclosedD]
      change PrimeSpectrum.comap (g.comp (algebraMap C D')) y ∈
        closedPoints (PrimeSpectrum C)
      rwa [PrimeSpectrum.comap_comp_apply, hyq']
    refine ⟨y, hyclosed, ?_⟩
    calc
      PrimeSpectrum.comap (algebraMap B D) y =
          PrimeSpectrum.comap (algebraMap B D') (PrimeSpectrum.comap g y) := by
            change PrimeSpectrum.comap (g.comp (algebraMap B D')) y = _
            rw [← PrimeSpectrum.comap_comp_apply]
      _ = x := by rw [hyq', hq'B]
  have hD'indEt : ObjectProperty.ind.{u}
      (fun E : Under (CommRingCat.of D') ↦ E.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom g)) :=
    indZariski_under_to_indEtale D' D hD'indZ
  have hBDindUnder := indUnder_of_ind_etale_commAlgCat B D <|
    CommAlgCat.ind_etale_comp hBD'ind (ind_etale_commAlgCat_of_indUnder D' D hD'indEt)
  have hBDflat : (algebraMap B D).Flat :=
    flat_comp_indZariski (algebraMap B D') (RingHom.FaithfullyFlat.flat hBD'ff) hD'indZ
  have hBDff : (algebraMap B D).FaithfullyFlat :=
    ((faithfullyFlat_tfae00HQ (algebraMap B D) hBDflat).out 1 3).mpr (by
      intro x hx
      obtain ⟨y, _, hyx⟩ := hclosedSurjB x
      exact ⟨y, hyx⟩)
  exact ⟨C, D, hC, hD, algAC, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    hACff, hACind, hBDff, hBDindUnder, hWC, hWD, hWmap, hclosedD,
    hclosedSurjA, hclosedSurjB, hCstrict⟩

end AlgebraicGeometry.ProEtale

end

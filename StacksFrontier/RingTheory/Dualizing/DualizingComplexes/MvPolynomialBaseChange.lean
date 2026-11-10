module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing complexes over polynomial rings in finitely many variables

A dualizing complex over a Noetherian ring stays dualizing after derived extension of scalars to
the polynomial algebra `R[x_1, …, x_n]`. This is [Stacks, Tag 0A7J]
(`Dualizing.polynomialBaseChange_isDualizingComplex`, the one-variable case) iterated `n` times.

## Main definitions

* `Dualizing.mvPolynomialExtension` — extension of scalars along `MvPolynomial.C`, on derived
  categories. The ring map is flat because `MvPolynomial (Fin n) R` is a free `R`-algebra, so
  degreewise extension of scalars is exact and descends to the derived category.

## Main results

* `Dualizing.mvPolynomialBaseChange_isDualizingComplex` — the derived extension of a dualizing
  complex to `R[x_1, …, x_n]` is dualizing.

## Implementation notes

The induction splits `MvPolynomial (Fin (n + 1)) R ≃+* Polynomial (MvPolynomial (Fin n) R)` with
`MvPolynomial.finSuccEquiv`. Each step therefore needs two transports: one comparing the lifted
model `Dualizing.polynomialBaseChange` of the one-variable statement with ordinary extension of
scalars in a single universe (`Dualizing.polynomialBaseChangeIso`), and one moving coefficients
along a ring isomorphism (`Dualizing.isDualizingComplex_restrictScalars`). Both comparisons are
obtained from uniqueness of left adjoints, so what has to be checked by hand each time is only the
compatibility of the ring maps, which is `MvPolynomial.finSuccEquiv_comp_C_eq_C`.

Several ingredients are `private` in
`StacksFrontier/RingTheory/Dualizing/DualizingComplexes/PolynomialBaseChange.lean` and are reached
by
`import all` rather than re-proved, in the same way as
`StacksFrontier/RingTheory/Dualizing/LocalizationAwayDualizing.lean` and
`StacksFrontier/RingTheory/Dualizing/NormalizedShift.lean`:
`Dualizing.isDualizingComplex_of_iso`, the two `mapDerivedCategory` transports of finite injective
dimension and finite cohomology, and the restriction-of-scalars transports of finiteness and of
the homothety condition. A name reached that way may be used inside a proof but may not appear in
an exposed `def` body, which is why only theorems below use them.

No `@[stacks]` attribute appears here: 0A7J is already attributed in
`StacksFrontier/RingTheory/Dualizing/DualizingComplexes/PolynomialBaseChange.lean`, and what is new
here is its iteration.

## References

* [Stacks Project, Tag 0A7J](https://stacks.math.columbia.edu/tag/0A7J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe u

/-- Moving the coefficients of a dualizing complex along a ring isomorphism gives a dualizing
complex. -/
private theorem isDualizingComplex_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) (hK : IsDualizingComplex K) :
    IsDualizingComplex
      ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj K) := by
  let F := ModuleCat.restrictScalars.{u} e.toRingHom
  let G := ModuleCat.restrictScalars.{u} e.symm.toRingHom
  let : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let : G.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e.symm
  let : F.PreservesInjectiveObjects := inferInstance
  let : G.PreservesInjectiveObjects := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact finiteInjectiveDimension_mapDerivedCategory F (fun M hM ↦
      ⟨0, (injective_iff_hasInjectiveDimensionLE_zero (F.obj M)).mp
        (F.injective_obj_of_injective hM)⟩) K hK.finiteInjectiveDimension
  · refine finiteCohomology_mapDerivedCategory F ?_ K hK.finiteCohomology
    intro M hM
    let : Module.Finite S M := hM
    exact finite_restrictScalars_of_ringEquiv e M
  · rintro I ⟨eI⟩ hinj ⟨a, b, hge, hle⟩
    let J : CochainComplex (ModuleCat.{u} S) ℤ :=
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    have hinjJ (i : ℤ) : Injective (J.X i) := G.injective_obj_of_injective (hinj i)
    have hgeJ : J.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff J a).mpr fun i hi ↦
      G.map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp hge i hi)
    have hleJ : J.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff J b).mpr fun i hi ↦
      G.map_isZero ((CochainComplex.isStrictlyLE_iff I b).mp hle i hi)
    let eJ : DerivedCategory.Q.obj J ≅ K :=
      (G.mapDerivedCategoryFactors.app I).symm ≪≫
        G.mapDerivedCategory.mapIso eI ≪≫ derivedRestrictScalarsUnitIso e K
    exact homothetyQuasiIso_of_restrictScalars_general e.symm I
      (hK.homothetyQuasiIso J ⟨eJ⟩ hinjJ ⟨a, b, hgeJ, hleJ⟩)

/-- In a single universe the lifted model `Dualizing.polynomialBaseChange` agrees with ordinary
extension of scalars along `Polynomial.C`; the comparison comes from uniqueness of left
adjoints. -/
private noncomputable def polynomialBaseChangeIso {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    letI : PreservesFiniteLimits
        (ModuleCat.extendScalars.{u, u, u} (Polynomial.C : R →+* Polynomial R)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    polynomialBaseChange K ≅
      (ModuleCat.extendScalars.{u, u, u}
        (Polynomial.C : R →+* Polynomial R)).mapDerivedCategory.obj K := by
  let R' := ULift.{u} R
  let e : R' ≃+* R := ULift.ringEquiv
  let p : Polynomial R ≃+* Polynomial R' := Polynomial.mapEquiv e.symm
  let U := ModuleCat.uliftFunctor.{u, u} R
  let E₁ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let E₂ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv p
  let C := ModuleCat.restrictScalars.{u} e.toRingHom
  let F := ModuleCat.extendScalars.{u, u, u} (Polynomial.C : R' →+* Polynomial R')
  let G := ModuleCat.restrictScalars.{u} p.toRingHom
  let H := ModuleCat.extendScalars.{u, u, u} (Polynomial.C : R →+* Polynomial R)
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : PreservesFiniteLimits H :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let adj := (E₁.toAdjunction.comp (ModuleCat.extendRestrictScalarsAdj
    (Polynomial.C : R' →+* Polynomial R'))).comp E₂.toAdjunction
  let r : E₂.inverse ⋙ ModuleCat.restrictScalars (Polynomial.C : R' →+* Polynomial R') ⋙
      E₁.inverse ≅ ModuleCat.restrictScalars (Polynomial.C : R →+* Polynomial R) := by
    refine (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.restrictScalarsComp _ _).symm _ ≪≫ ?_
    exact (ModuleCat.restrictScalarsComp' _ _ _ (by ext x; simp [p, e])).symm
  let t : (C ⋙ F) ⋙ G ≅ H :=
    Adjunction.leftAdjointUniq (adj.ofNatIsoRight r)
      (ModuleCat.extendRestrictScalarsAdj (Polynomial.C : R →+* Polynomial R))
  let ui : U ≅ 𝟭 (ModuleCat.{u} R) :=
    NatIso.ofComponents (fun M ↦ ULift.moduleEquiv.toModuleIso) (by intros; rfl)
  let a : U ⋙ (C ⋙ F) ≅ C ⋙ F :=
    Functor.isoWhiskerRight ui _ ≪≫ Functor.leftUnitor _
  let t' : (U ⋙ (C ⋙ F)) ⋙ G ≅ H := Functor.isoWhiskerRight a _ ≪≫ t
  change G.mapDerivedCategory.obj
    (F.mapDerivedCategory.obj (C.mapDerivedCategory.obj (U.mapDerivedCategory.obj K))) ≅ _
  exact G.mapDerivedCategory.mapIso
    ((mapDerivedCategoryCompNatIso C F (C ⋙ F) (Iso.refl _)).app
      (U.mapDerivedCategory.obj K)) ≪≫
    G.mapDerivedCategory.mapIso
      ((mapDerivedCategoryCompNatIso U (C ⋙ F) (U ⋙ (C ⋙ F)) (Iso.refl _)).app K) ≪≫
    (mapDerivedCategoryCompNatIso (U ⋙ (C ⋙ F)) G H t').app K

/-- Exact extension of scalars from `R` to the polynomial algebra in `n` variables, on derived
categories. -/
noncomputable def mvPolynomialExtension (R : Type u) [CommRing R] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) R)) :=
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  (ModuleCat.extendScalars.{u, u, u}
    (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)).mapDerivedCategory

/-- Derived extension of scalars to `R[x_1, …, x_n]` sends a dualizing complex to a dualizing
complex; this iterates the one-variable statement [stacks 0A7J]. -/
theorem mvPolynomialBaseChange_isDualizingComplex {R : Type u} [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsDualizingComplex K) :
    IsDualizingComplex ((mvPolynomialExtension R n).obj K) := by
  induction n with
  | zero =>
    let e : MvPolynomial (Fin 0) R ≃+* R :=
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv
    let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
    let F := ModuleCat.extendScalars.{u, u, u}
      (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R)
    let : PreservesFiniteLimits F :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    let r : E.inverse ≅ ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R) :=
      eqToIso (congrArg ModuleCat.restrictScalars
        (rfl : e.symm.toRingHom = (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R)))
    let t : E.functor ≅ F := Adjunction.leftAdjointUniq
      (E.toAdjunction.ofNatIsoRight r) (ModuleCat.extendRestrictScalarsAdj _)
    exact isDualizingComplex_of_iso ((mapDerivedCategoryNatIso E.functor F t).app K)
      (isDualizingComplex_restrictScalars e K hK)
  | succ n ih =>
    let P := MvPolynomial (Fin n) R
    let Q := MvPolynomial (Fin (n + 1)) R
    let e : Q ≃+* Polynomial P := (MvPolynomial.finSuccEquiv R n).toRingEquiv
    let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
    let f : R →+* P := MvPolynomial.C
    let g : P →+* Polynomial P := Polynomial.C
    let h : R →+* Q := MvPolynomial.C
    let F := ModuleCat.extendScalars.{u, u, u} f
    let G := ModuleCat.extendScalars.{u, u, u} g
    let H := ModuleCat.extendScalars.{u, u, u} h
    let : PreservesFiniteLimits F :=
      extendScalars_preservesFiniteLimits_of_flat' f
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    let : PreservesFiniteLimits G :=
      extendScalars_preservesFiniteLimits_of_flat' g
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    let : PreservesFiniteLimits H :=
      extendScalars_preservesFiniteLimits_of_flat' h
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    have hpoly : IsDualizingComplex
        (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
      isDualizingComplex_of_iso (polynomialBaseChangeIso _)
        (polynomialBaseChange_isDualizingComplex _ ih)
    let adj := ((ModuleCat.extendRestrictScalarsAdj f).comp
      (ModuleCat.extendRestrictScalarsAdj g)).comp E.toAdjunction
    let r : E.inverse ⋙ ModuleCat.restrictScalars g ⋙ ModuleCat.restrictScalars f ≅
        ModuleCat.restrictScalars h :=
      Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp f g).symm ≪≫
        (ModuleCat.restrictScalarsComp' (g.comp f) e.symm.toRingHom h
          (MvPolynomial.finSuccEquiv_comp_C_eq_C n).symm).symm
    let t : (F ⋙ G) ⋙ E.functor ≅ H :=
      Adjunction.leftAdjointUniq (adj.ofNatIsoRight r) (ModuleCat.extendRestrictScalarsAdj h)
    let i : F.mapDerivedCategory ⋙ G.mapDerivedCategory ⋙ E.functor.mapDerivedCategory ≅
        H.mapDerivedCategory :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryCompNatIso F G (F ⋙ G) (Iso.refl _)) _ ≪≫
        mapDerivedCategoryCompNatIso (F ⋙ G) E.functor H t
    exact isDualizingComplex_of_iso (i.app K) (isDualizingComplex_restrictScalars e _ hpoly)

end Dualizing

end

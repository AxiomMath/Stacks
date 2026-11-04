module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalization
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.FormalFibres.EssFiniteType
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.FormalFibres.EssFiniteType

/-!
# Gorenstein formal fibres of a ring with a dualizing complex

Let `A` be a Noetherian local ring. The *formal fibre* of `A` at a prime `𝔭` is the ring
`Â ⊗_A κ(𝔭)`, where `Â` is the completion of `A` at its maximal ideal and `κ(𝔭)` is the residue
field of `A` at `𝔭`. If `A` admits a dualizing complex, then every formal fibre of `A` is a
Gorenstein ring.

The formal fibre at `𝔭` only depends on `A/𝔭`, so one may replace `A` by a localization of
`A/𝔭` and assume `𝔭 = (0)`, the ring a domain and the fibre the generic one `D ⊗_Q K` with `K`
the fraction field of the domain `Q` and `D` a completion. A dualizing complex `ω` on `Q`
pushes forward to one on `K`; over a field a dualizing complex is a shift of the field, and
pushing that shift forward along `K → D ⊗_Q K` exhibits the generic fibre, in degree zero, as a
shift of a dualizing complex over itself. Shifts of dualizing complexes are dualizing, so the
generic fibre is its own dualizing complex, and that is Gorensteinness.

## Main results

* `Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex` — the formal fibre of a
  Noetherian local ring admitting a dualizing complex is Gorenstein at every prime.
* `Dualizing.isGorensteinRing_of_isDualizingComplex_self` — a Noetherian ring that, in degree
  zero, is a dualizing complex over itself is Gorenstein.
* `Dualizing.gorensteinTarget` — Gorensteinness of the target, as a `RingMapProperty`.

## Implementation notes

Gorensteinness is only defined for Noetherian rings, so the conclusion carries the Noetherian
structure of the formal fibre as part of the existential statement.

The reduction to the generic fibre of a prime quotient is the quotient-completion criterion
`propertyRing_iff_quotientCompletion_fibers`, applied to the property of a ring map whose target
is a Noetherian Gorenstein ring. The module universe of the dualizing complex is the ring's own,
which is the universe at which `Dualizing.IsGorensteinLocalRing` is itself stated.

## References

* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7I](https://stacks.math.columbia.edu/tag/0A7I)
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory IsLocalRing
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

/-- The universe lift inside derived extension of scalars is invisible when the two rings and
the module carrier share one universe. -/
private def pseudoExtensionToTotalIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj K ≅
      (totalDerivedExtensionScalars.{u, u, u} f).functor.obj K := by
  change (totalDerivedExtensionScalars.{u, u, u} f).functor.obj
      ((ModuleCat.uliftFunctor.{u, u} R).mapDerivedCategory.obj K) ≅ _
  exact (totalDerivedExtensionScalars.{u, u, u} f).functor.mapIso ((uliftDerivedSelfIso R).app K)

/-- For a flat ring map, degreewise extension of scalars is exact, hence is its own total left
derived functor; so it agrees with derived extension of scalars. -/
private def directExtensionScalarsFlatIso {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (_hf : (algebraMap R S).Flat)
    [hPres : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S))]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap R S)).obj K ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapDerivedCategory.obj K := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let D := totalDerivedExtensionScalars.{u, u, u} (algebraMap R S)
  letI : PreservesFiniteLimits F := hPres
  haveI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
  let eDerived : D.functor ≅ F.mapDerivedCategory := by
    let htarget : CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
        (algebraMap R S) ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
      Iso.refl _
    exact Functor.leftDerivedNatIso D.functor F.mapDerivedCategory D.comparison
      F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) htarget
  let U := ModuleCat.uliftFunctor.{u, u} R
  change D.functor.obj (U.mapDerivedCategory.obj K) ≅ F.mapDerivedCategory.obj K
  exact eDerived.app (U.mapDerivedCategory.obj K) ≪≫
    F.mapDerivedCategory.mapIso ((uliftDerivedSelfIso R).app K)

/-- Derived extension of scalars carries the source ring, in degree zero, to the target ring, in
degree zero: the ring is a K-flat complex, so the comparison with degreewise extension of scalars
is an isomorphism there, and degreewise extension of scalars sends `R` to `S`. -/
private def totalExtensionScalarsUnitIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) := by
  letI := f.toAlgebra
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, u, u} f
  let unitR := ModuleCat.of R R
  let P : CochainComplex (ModuleCat.{u} R) ℤ := 𝟙_ _
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P fun K hK =>
    HomologicalComplex.Acyclic.of_iso (MonoidalCategory.rightUnitor K).symm hK
  exact D.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app unitR) ≪≫
    asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app unitR) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj unitR)).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- Derived extension of scalars along `f : R →+* S` carries `R`, in degree zero, to `S`, in
degree zero. -/
private def extensionScalarsUnitIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) :=
  pseudoExtensionToTotalIso f _ ≪≫ totalExtensionScalarsUnitIso f

/-- Total derived extension of scalars along `f` and then `g` is total derived extension of
scalars along any ring map equal to `g.comp f`. -/
private def totalDerivedExtensionScalarsCompIso {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} {h : R →+* T} (hfg : g.comp f = h)
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X) ≅
      (totalDerivedExtensionScalars.{u, u, u} h).functor.obj X := by
  subst hfg
  exact (StacksDraft.Perfect.derivedExtensionScalarsComp.{u, u} f g).app X

/-- Pseudo-coherent derived extension of scalars along `f` and then `g` is the one along any ring
map equal to `g.comp f`. -/
private def pseudoExtensionScalarsCompIso {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} {h : R →+* T} (hfg : g.comp f = h)
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars g).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj X) ≅
      (StacksDraft.PseudoCoherence.derivedExtensionScalars h).obj X :=
  pseudoExtensionToTotalIso g _ ≪≫
    (totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso (pseudoExtensionToTotalIso f X) ≪≫
    totalDerivedExtensionScalarsCompIso hfg X ≪≫ (pseudoExtensionToTotalIso h X).symm

/-- Over a field, a dualizing complex is a shift of the field in degree zero. -/
private theorem exists_iso_shift_of_isDualizingComplex_field {F : Type u} [Field F]
    (ω : DerivedCategory (ModuleCat.{u} F)) (h : IsDualizingComplex ω) :
    ∃ n : ℤ, Nonempty
      (ω ≅ ((DerivedCategory.singleFunctor (ModuleCat.{u} F) 0).obj (ModuleCat.of F F))⟦n⟧) := by
  have : Simple ω := simple_of_isDualizingComplex_field.{u, u} ω h
  obtain ⟨a, b, I, hge, hle, _, ⟨eI⟩⟩ := h.finiteInjectiveDimension
  have := hge
  have := hle
  have : ω.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have : ω.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eI.symm b
  obtain ⟨n, ⟨e⟩⟩ := simple_bounded_iso_shift_field.{u, u} ω a b
  exact ⟨n, ⟨e ≪≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} F)) n).mapIso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} F) 0).mapIso
      (ULift.moduleEquiv (R := F) (M := F)).toModuleIso)⟩⟩

/-- **A Noetherian ring which is its own dualizing complex is Gorenstein.** Being a dualizing
complex survives localization, and the localization of the ring in degree zero is the localized
ring in degree zero, so every local ring of `R` is its own dualizing complex. -/
theorem isGorensteinRing_of_isDualizingComplex_self (R : Type u) [CommRing R]
    [IsNoetherianRing R]
    (h : IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :
    IsGorensteinRing R := by
  intro q hq
  let : q.IsPrime := hq
  exact isDualizingComplex_of_iso
    (extensionScalarsUnitIso (algebraMap R (Localization.AtPrime q)))
    (isDualizingComplex_localization (B := Localization.AtPrime q) q.primeCompl _ h)

/-- **A Noetherian ring with a dualizing complex that is a shift of the ring is Gorenstein.**
Shifting back is again dualizing, and a shift of a shift by the opposite amount is the original
object. -/
private theorem isGorensteinRing_of_isDualizingComplex_shift_self (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℤ)
    (h : IsDualizingComplex
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦n⟧)) :
    IsGorensteinRing R := by
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  exact isGorensteinRing_of_isDualizingComplex_self R (isDualizingComplex_of_iso
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) n (-n) (by omega)).app U)
    (isDualizingComplex_shift (U⟦n⟧) h (-n)))

/-- Being a Noetherian Gorenstein ring, viewed as a property of the target of a ring
homomorphism. This is the concrete `RingMapProperty` at which
`Dualizing.gorensteinTarget_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJN]) states the five
axioms of [Stacks, Tag 0BIR]. -/
def gorensteinTarget : RingMapProperty.{u, u} where
  property := fun {_ B} _ _ _ => ∃ h : IsNoetherianRing B, @IsGorensteinRing B inferInstance h
  respectsIso := by
    refine ⟨?_, ?_⟩
    · intro A B C _ _ _ f e h
      obtain ⟨hB, hG⟩ := h
      let : IsNoetherianRing B := hB
      let : IsNoetherianRing C := isNoetherianRing_of_ringEquiv B e
      exact ⟨inferInstance, isGorensteinRing_of_ringEquiv e hG⟩
    · intro A B C _ _ _ f e h
      exact h

/-- For a local ring, the formal fibres of the ring and of its localization at the maximal ideal
carry the same properties: the two rings are isomorphic. -/
private theorem formalFibersHave_of_localizationAtMaximal (P : RingMapProperty.{u, u})
    (R : Type u) [CommRing R] [IsLocalRing R]
    (h : FormalFibersHave P (Localization.AtPrime (maximalIdeal R))) :
    FormalFibersHave P R := by
  let M := (maximalIdeal R).primeCompl
  let : IsLocalization M R := IsLocalization.self fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx
  let e : Localization.AtPrime (maximalIdeal R) ≃+* R :=
    (IsLocalization.algEquiv M (Localization.AtPrime (maximalIdeal R)) R).toRingEquiv
  intro q
  exact (P.ulift_iff _).mp (Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, u, 0, 0} P e
    (fun q => (P.ulift_iff _).mpr (h q)) q)

/-- **The generic fibre of a flat algebra over a Noetherian domain with a dualizing complex is
Gorenstein.** The dualizing complex pushes forward to a dualizing complex over the fraction
field; over a field a dualizing complex is a shift of the field, and pushing that shift forward
to the generic fibre identifies a dualizing complex there with a shift of the fibre itself. -/
private theorem isGorensteinRing_genericFibre
    {Q D F : Type u} [CommRing Q] [CommRing D] [Field F]
    [IsDomain Q] [IsNoetherianRing Q] [IsNoetherianRing D]
    [Algebra Q D] [Algebra Q F] [IsFractionRing Q F]
    (ω : DerivedCategory (ModuleCat.{u} Q)) (hω : IsDualizingComplex ω)
    (hD : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q D)).obj ω)) :
    ∃ h : IsNoetherianRing (D ⊗[Q] F), @IsGorensteinRing (D ⊗[Q] F) inferInstance h := by
  let M : Submonoid Q := nonZeroDivisors Q
  let L := D ⊗[Q] F
  let N : Submonoid D := Algebra.algebraMapSubmonoid D M
  let : Algebra D L := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower Q D L := inferInstance
  let : IsScalarTower Q F L := inferInstance
  let : IsLocalization N L :=
    (Algebra.isLocalization_iff_isPushout M F).mpr inferInstance
  have hLNoeth : IsNoetherianRing L := IsLocalization.isNoetherianRing N L inferInstance
  -- The dualizing complex of `Q` pushed forward to the fraction field, and on to `L`.
  have hF : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q F)).obj ω) :=
    isDualizingComplex_localization (B := F) M ω hω
  -- Over a field, a dualizing complex is a shift of the field.
  obtain ⟨n, ⟨eF⟩⟩ := exists_iso_shift_of_isDualizingComplex_field _ hF
  -- Transport the shift along `F → L`.
  let EFL := totalDerivedExtensionScalars.{u, u, u} (algebraMap F L)
  let EQL := totalDerivedExtensionScalars.{u, u, u} (algebraMap Q L)
  let := EFL.commShift
  let UF : DerivedCategory (ModuleCat.{u} F) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} F) 0).obj (ModuleCat.of F F)
  let UL : DerivedCategory (ModuleCat.{u} L) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} L) 0).obj (ModuleCat.of L L)
  -- The dualizing complex of `L` obtained through `D`, read through `F`.
  have hDL : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap D L)).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q D)).obj ω)) :=
    isDualizingComplex_localization (B := L) N _ hD
  have hQL : IsDualizingComplex (EQL.functor.obj ω) := isDualizingComplex_of_iso
    (pseudoExtensionScalarsCompIso (IsScalarTower.algebraMap_eq Q D L).symm ω ≪≫
      pseudoExtensionToTotalIso (algebraMap Q L) ω) hDL
  -- The same dualizing complex, read through `F`, is a shift of `L` in degree zero.
  have eQL : EQL.functor.obj ω ≅ UL⟦n⟧ :=
    (totalDerivedExtensionScalarsCompIso (IsScalarTower.algebraMap_eq Q F L).symm ω).symm ≪≫
      EFL.functor.mapIso ((pseudoExtensionToTotalIso (algebraMap Q F) ω).symm ≪≫ eF) ≪≫
      (EFL.functor.commShiftIso n).app UF ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} L)) n).mapIso
        (totalExtensionScalarsUnitIso (algebraMap F L))
  exact ⟨hLNoeth, isGorensteinRing_of_isDualizingComplex_shift_self L n
    (isDualizingComplex_of_iso eQL hQL)⟩

/-- **Stacks Project, Tag 0AWY.** Every formal fibre of a Noetherian local ring admitting a
dualizing complex is Gorenstein. -/
@[stacks 0AWY]
theorem isGorensteinRing_formalFibre_of_isDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K)
    (p : Ideal A) [p.IsPrime] :
    ∃ h : IsNoetherianRing (AdicCompletion (maximalIdeal A) A ⊗[A] p.ResidueField),
      @IsGorensteinRing (AdicCompletion (maximalIdeal A) A ⊗[A] p.ResidueField)
        inferInstance h := by
  let P : RingMapProperty.{u, u} := gorensteinTarget
  have hring : IsPRing P A := by
    refine (propertyRing_iff_quotientCompletion_fibers P).mpr ?_
    intro pp qq hqp
    dsimp only
    let Q := A ⧸ qq.asIdeal
    let S := Localization
      (Submonoid.map (Ideal.Quotient.mk qq.asIdeal) pp.asIdeal.primeCompl)
    let J : Ideal S :=
      (pp.asIdeal.map (Ideal.Quotient.mk qq.asIdeal)).map (algebraMap Q S)
    let D := AdicCompletion J S
    let : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing qq.asIdeal
    let : IsDomain Q := Ideal.Quotient.isDomain qq.asIdeal
    let : IsNoetherianRing S :=
      IsLocalization.isNoetherianRing
        (Submonoid.map (Ideal.Quotient.mk qq.asIdeal) pp.asIdeal.primeCompl) S inferInstance
    let : IsNoetherianRing D := AdicCompletion.isNoetherianRing J
    let : Module.Flat S D := AdicCompletion.flat_of_isNoetherian J
    have hflat : (algebraMap S D).Flat :=
      RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S D)
    let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap S D)) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    -- The dualizing complex of `A` descends to the prime quotient and its localization.
    let ω := (derivedHom.{u, u, u} (Ideal.Quotient.mk qq.asIdeal)).obj K
    have hω : IsDualizingComplex ω :=
      isDualizingComplex_derivedHom_of_finite.{u, u} (Ideal.Quotient.mk qq.asIdeal)
        (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) K hK
    have hS : IsDualizingComplex
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q S)).obj ω) :=
      isDualizingComplex_localization (B := S)
        (Submonoid.map (Ideal.Quotient.mk qq.asIdeal) pp.asIdeal.primeCompl) ω hω
    -- and on to the completion.
    have hD₀ : IsDualizingComplex
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap S D)).mapDerivedCategory.obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q S)).obj ω)) :=
      isDualizingComplex_adicCompletion J _ hS
    have hD : IsDualizingComplex
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q D)).obj ω) :=
      isDualizingComplex_of_iso ((directExtensionScalarsFlatIso hflat
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap Q S)).obj ω)).symm ≪≫
        pseudoExtensionScalarsCompIso (IsScalarTower.algebraMap_eq Q S D).symm ω) hD₀
    exact isGorensteinRing_genericFibre (F := qq.asIdeal.ResidueField) ω hω hD
  have hm := hring.2 ⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩
  exact formalFibersHave_of_localizationAtMaximal P A hm ⟨p, inferInstance⟩

end Dualizing

end

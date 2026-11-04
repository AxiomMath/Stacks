module

public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DiagonalModelHom
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativePerfection
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative dualizing complex has finite Tor dimension over the base

Let `φ : R → A` be a perfect homomorphism of finite type of Noetherian rings and let
`ω^•_{A/R} = φ^!(R)` be its relative dualizing complex.  This file proves that `ω^•_{A/R}` has
finite Tor dimension as a complex of `R`-modules, which is [stacks 0BZW] (1)(b), and deduces
[stacks 0BZW] (2)(a) — relative perfection of `ω^•_{A/R}` for a *flat* `φ` — from it with no
hypothesis carried.

## Main definitions

There are no new definitions.

## Main results

* `Dualizing.isPerfect_modelHom_single_self` — the internal derived dual
  `RHom_P(K, P)` of [stacks 0A63], taken at the canonical model bifunctor over `P` itself, is
  perfect when `K` is.  This is [stacks 07VI] for that bifunctor.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_restrictScalars_isPerfect` —
  `ω^•_{A/R}` is a perfect object of `D(P)` for the polynomial algebra `P` of the presentation.
* `PolynomialPresentation.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap` —
  **[stacks 0BZW] (1)(b)**.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect` —
  **[stacks 0BZW] (2)(a)**: for a flat `φ`, `ω^•_{A/R}` is perfect relative to `R`.

## Implementation notes

The argument is the source's, and it is the same argument that gives [stacks 0BZW] (1)(c).
Unwinding `φ^!` at the base ring, `ω^•_{A/R}` is a shift of the derived coextension
`RHom_P(A, P)` along the presentation's surjection `P ↠ A`, by
`Dualizing.PolynomialPresentation.derivedExtensionUnitIso`.  Restricted to `P` that coextension
is the *internal* derived Hom of [stacks 0A63] out of `A` read over `P`, which is
`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`; it is perfect in `D(P)` because `A` is,
which is [stacks 07VI]; and `R → P` is flat, so a bounded complex of finite projective
`P`-modules restricts to a bounded complex of flat `R`-modules, which is finite Tor dimension by
[stacks 0654].

### What this removes

The module documentation of `StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing`
recorded (1)(b) as unavailable, for one reason: that the library's [stacks 07VI] is stated for
`StacksDraft.Perfect.derivedDual`, the internal Hom of the ULift-transported adjunction
`StacksDraft.DerivedHom.derivedHomAdjunctionULift` over `ULift P`, and that nothing identified
that with the internal Hom of `StacksDraft.DerivedHom.DerivedInternalHom.Model` over `P`.  That
identification is not needed: `Dualizing.isPerfect_modelHom_single_self` below proves the one
consequence of [stacks 07VI] the argument uses — perfectness of the dual — directly at the model
bifunctor, from the comparison of [stacks 0A66]
(`StacksDraft.DerivedHom.projectiveHomComparison`), which is stated at that bifunctor.  The dual
of a bounded complex of finite projectives is the Hom complex into the unit, whose terms are the
`P`-linear duals of the terms, and those are again finite projective.

Consequently [stacks 0BZW] (2)(a) is unconditional here.  It was already available as
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect_of_flat` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativePerfection`, by the fibrewise criterion
[stacks 0GHJ] and base change [stacks 0BZV], but that route carries the open projection-formula
compatibility `Dualizing.PolynomialPresentation.ProjectionCompatibility` at every residue field of
`R`.  Nothing is carried below.  Both statements are kept: that one is proved from a hypothesis
on the presentation square alone and is the statement the fibrewise criterion gives, this one is
the source's route.

### Duplication this module introduces, and why

`Dualizing.isPerfect_of_iso` and `Dualizing.isPerfect_shift` restate the invariance of
perfectness under isomorphism and shift, which `StacksFrontier.Homology.Perfect.Basic` has as
`private lemma isPerfect_of_iso` and `private lemma isPerfect_shift` and so cannot be cited from
here; they are kept private.  Promoting those two is a dedup target, and the same two restatements
occur in `StacksFrontier/Homology/Perfect/MinimalRepresentative.lean:3163` and in several other files.

### Universes

The module universe is the ring universe, as in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativePerfection`; the statements of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing` at an independent module universe
are transported along `ULift.moduleEquiv` where they are consumed.

## References

* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0DHS](https://stacks.math.columbia.edu/tag/0DHS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### Invariance of perfectness under isomorphism and shift -/

/-- Perfectness is invariant under isomorphism in the derived category. -/
private theorem isPerfect_of_iso {P : Type u} [CommRing P]
    {K L : DerivedCategory (ModuleCat.{u} P)} (e : K ≅ L)
    (hL : StacksDraft.Perfect.IsPerfect L) : StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨E, a, b, ha, hb, hf, hp, ⟨e'⟩⟩ := hL
  exact ⟨E, a, b, ha, hb, hf, hp, ⟨e ≪≫ e'⟩⟩

/-- Perfectness is invariant under shift: shift a bounded finite projective representative. -/
private theorem isPerfect_shift {P : Type u} [CommRing P]
    (K : DerivedCategory (ModuleCat.{u} P)) (n : ℤ)
    (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.Perfect.IsPerfect (K⟦n⟧) := by
  obtain ⟨E, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := hK
  exact ⟨E⟦n⟧, a - n, b - n,
    E.isStrictlyGE_shift a n (a - n) (by omega),
    E.isStrictlyLE_shift b n (b - n) (by omega),
    fun i => hf _, fun i => hp _,
    ⟨(shiftFunctor _ n).mapIso e ≪≫ (DerivedCategory.Q.commShiftIso n).symm.app E⟩⟩

/-! ### Perfectness of the internal derived dual -/

/-- A bounded complex of finite projectives representing `K` in `[a, b]` gives one representing
the derived dual `RHom_P(K, P)` in `[-b, -a]`. -/
private theorem exists_finiteProjectiveRepresentative_modelHom_of_iso {P : Type u} [CommRing P]
    (K : DerivedCategory (ModuleCat.{u} P)) (E : CochainComplex (ModuleCat.{u} P) ℤ) (a b : ℤ)
    (hfp : ∀ i : ℤ, Module.Finite P (E.X i) ∧ Module.Projective P (E.X i))
    (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b) (e : K ≅ DerivedCategory.Q.obj E) :
    ∃ H : CochainComplex (ModuleCat.{u} P) ℤ,
      (∀ i : ℤ, Module.Finite P (H.X i) ∧ Module.Projective P (H.X i)) ∧
        H.IsStrictlyGE (-b) ∧ H.IsStrictlyLE (-a) ∧
          Nonempty ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom P).obj
            (Opposite.op K, (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
              (ModuleCat.of P P)) ≅ DerivedCategory.Q.obj H) := by
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  have (i : ℤ) := (hfp i).1
  have (i : ℤ) := (hfp i).2
  refine ⟨CochainComplex.HomComplexR P E J, fun i => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (StacksDraft.Perfect.homComplexTermLinearEquiv E i).symm
  · exact Module.Projective.of_equiv (StacksDraft.Perfect.homComplexTermLinearEquiv E i).symm
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact StacksDraft.Perfect.homComplexTerm_isZero E i (E.isZero_of_isStrictlyLE b (-i) (by omega))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact StacksDraft.Perfect.homComplexTerm_isZero E i (E.isZero_of_isStrictlyGE a (-i) (by omega))
  · exact ⟨(StacksDraft.DerivedHom.derivedHomAdjunction (R := P)).hom.mapIso
        (e.symm.op.prod (Iso.refl _)) ≪≫
      StacksDraft.DerivedHom.projectiveHomComparison.iso E J b⟩

/-- **[stacks 07VI] for the internal derived Hom of [stacks 0A63] over `P` itself.**  The derived
dual `RHom_P(K, P)` of a perfect object of `D(P)`, formed at the canonical model bifunctor
`StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`, is perfect.

A bounded complex `E` of finite projective `P`-modules representing `K` computes the internal
derived Hom against every target by [stacks 0A66],
`StacksDraft.DerivedHom.projectiveHomComparison`; against the unit the resulting Hom complex has
degree-`i` term the `P`-linear dual of `E_{-i}`, which is again finite projective
(`Module.dual_finite`, `Module.dual_projective`) and vanishes outside the reflected window. -/
@[sga "5 III 6.2" "special case", sga "6 I 7.3" "special case", sga "6 III 4.9.2" "special case"]
theorem isPerfect_modelHom_single_self {P : Type u} [CommRing P]
    (K : DerivedCategory (ModuleCat.{u} P)) (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.Perfect.IsPerfect
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom P).obj
        (Opposite.op K, (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
          (ModuleCat.of P P))) := by
  obtain ⟨E, a, b, hGE, hLE, hf, hp, ⟨e⟩⟩ := hK
  obtain ⟨H, hfp, h₁, h₂, he⟩ :=
    exists_finiteProjectiveRepresentative_modelHom_of_iso K E a b (fun i => ⟨hf i, hp i⟩) hGE hLE e
  exact ⟨H, -b, -a, h₁, h₂, fun i => (hfp i).1, fun i => (hfp i).2, he⟩

/-- **[stacks 07VI] over `P` itself, with the cohomological window tracked.**  A pseudo-coherent
object of `D(P)` with a flat representative in `[a, b]` — equivalently, by [stacks 0654], of Tor
amplitude in `[a, b]` — has a representative by a complex of finite projective `P`-modules
concentrated in `[a, b]`, which is the second half of [stacks 0658]
(`StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension`).  Its derived dual
`RHom_P(K, P)` is then represented by the Hom complex of that representative into the unit, a
complex of finite projective `P`-modules concentrated in the reflected window `[-b, -a]`.

This refines `Dualizing.isPerfect_modelHom_single_self`, which records the same conclusion with
the window existentially quantified; the window is what the Tor-amplitude clause of
[stacks 0E9Q] needs. -/
@[sga "5 III 6.2" "special case", sga "6 I 7.3" "special case", sga "6 III 4.9.2" "special case"]
theorem exists_finiteProjectiveRepresentative_modelHom_single_self {P : Type u} [CommRing P]
    (K : DerivedCategory (ModuleCat.{u} P)) (a b : ℤ)
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hflat : StacksDraft.Perfect.HasFlatRepresentative.{u, u} K a b) :
    ∃ H : CochainComplex (ModuleCat.{u} P) ℤ,
      (∀ i : ℤ, Module.Finite P (H.X i) ∧ Module.Projective P (H.X i)) ∧
        H.IsStrictlyGE (-b) ∧ H.IsStrictlyLE (-a) ∧
          Nonempty ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom P).obj
            (Opposite.op K, (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
              (ModuleCat.of P P)) ≅ DerivedCategory.Q.obj H) := by
  obtain ⟨E, hfp, hGE, hLE, ⟨e⟩⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} K).2 a b hpc
      hflat
  exact exists_finiteProjectiveRepresentative_modelHom_of_iso K E a b hfp hGE hLE e

/-! ### Finite Tor dimension of the relative dualizing complex -/

/-- **Restriction of a projective representative along a flat `R → P`.**  A complex of projective
`P`-modules concentrated in `[a, b]` restricts to a complex of `R`-modules concentrated in
`[a, b]` which are flat by transitivity — a flat representative over `R` in the same window, so
by [stacks 0654] Tor amplitude in `[a, b]` over `R`. -/
private theorem hasFlatRepresentative_restrictScalars_of_projectiveRepresentative
    {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    (L : DerivedCategory (ModuleCat.{u} P)) (a b : ℤ)
    (E : CochainComplex (ModuleCat.{u} P) ℤ)
    (hprojective : ∀ i : ℤ, Module.Projective P (E.X i))
    (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b) (e : L ≅ DerivedCategory.Q.obj E)
    (hflat : Module.Flat R P) :
    StacksDraft.TorAmplitude.HasFlatRepresentative
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) a b := by
  let U := ModuleCat.restrictScalars (algebraMap R P)
  let ER := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have hGER : CochainComplex.IsStrictlyGE ER a :=
    (CochainComplex.isStrictlyGE_iff ER a).mpr fun i hi =>
      U.map_isZero (E.isZero_of_isStrictlyGE a i hi)
  have hLER : CochainComplex.IsStrictlyLE ER b :=
    (CochainComplex.isStrictlyLE_iff ER b).mpr fun i hi =>
      U.map_isZero (E.isZero_of_isStrictlyLE b i hi)
  have hflatER : ∀ i : ℤ, Module.Flat R (ER.X i) := by
    intro i
    have : Module.Projective P (E.X i) := hprojective i
    let : Module R (E.X i) := (U.obj (E.X i)).isModule
    have : IsScalarTower R P (E.X i) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact Module.Flat.trans R P (E.X i)
  exact ⟨ER, hflatER, hGER, hLER,
    ⟨U.mapDerivedCategory.mapIso e ≪≫ U.mapDerivedCategoryFactors.app E⟩⟩

/-- A perfect object of `D(P)` for `P` flat over `R` restricts to an object of `D(R)` with a
bounded flat representative: restriction of scalars carries a bounded complex of finite
projective `P`-modules to a bounded complex of `R`-modules which are flat by transitivity. -/
@[sga "4½ Cycle 2.3.3" "partial", sga "6 I 5.0" "partial"]
private theorem hasFlatRepresentative_restrictScalars_of_isPerfect
    {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    (L : DerivedCategory (ModuleCat.{u} P)) (hL : StacksDraft.Perfect.IsPerfect L)
    (hflat : Module.Flat R P) :
    ∃ a b : ℤ, StacksDraft.TorAmplitude.HasFlatRepresentative
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) a b := by
  obtain ⟨E, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hL
  exact ⟨a, b, hasFlatRepresentative_restrictScalars_of_projectiveRepresentative L a b E
    hprojective hGE hLE e hflat⟩

/-- `PseudoCoherence.restrictScalarsDerivedCompIso` with the composite presented as a separate
homomorphism together with an equation, which is the form in which the presentation supplies it:
`Dualizing.PolynomialPresentation.commutes` identifies `R → A` with `R → P → A`. -/
private def restrictScalarsDerivedCompIsoOfEq {R P A : Type u} [CommRing R] [CommRing P]
    [CommRing A] (f : R →+* P) (g : P →+* A) (fg : R →+* A) (hfg : fg = g.comp f)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.restrictScalars.{u} fg).mapDerivedCategory.obj K ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj K) := by
  subst hfg
  exact PseudoCoherence.restrictScalarsDerivedCompIso f g K

/-- An object of `D(R)` isomorphic to the restriction of scalars of a perfect object of `D(P)`,
for `P` flat over `R`, has finite Tor dimension over `R`.  This is
`Dualizing.hasFlatRepresentative_restrictScalars_of_isPerfect` read through [stacks 0654]. -/
private theorem hasFiniteTorDimension_of_iso_restrictScalars_of_isPerfect
    {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    (K : DerivedCategory (ModuleCat.{u} R)) (L : DerivedCategory (ModuleCat.{u} P))
    (hL : StacksDraft.Perfect.IsPerfect L) (hflat : Module.Flat R P)
    (e : K ≅ (ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) :
    StacksDraft.TorAmplitude.HasFiniteTorDimension
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K := by
  obtain ⟨a, b, hrep⟩ := hasFlatRepresentative_restrictScalars_of_isPerfect L hL hflat
  exact ⟨a, b, (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K a b).2
    (StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso e.symm hrep)⟩

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Restricted to `P`, `ω^•_{A/R}` is the `n`-fold shift of the derived coextension of the unit. -/
private def restrictScalarsUpperShriekIsoShift (p : PolynomialPresentation (algebraMap R A)) :
    (ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
      (shiftFunctor (DerivedCategory (ModuleCat.{u} p.Poly)) (p.variableCount : ℤ)).obj
        ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
          ((derivedHom.{u, 0, u} p.toRingHom).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
              (ModuleCat.of p.Poly p.Poly)))) :=
  (ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.mapIso
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (p.variableCount : ℤ)).mapIso
        ((derivedHom.{u, 0, u} p.toRingHom).mapIso p.derivedExtensionUnitIso)) ≪≫
    ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.commShiftIso
      (p.variableCount : ℤ)).app _

/-- The structure map `R → A` factors through the polynomial algebra of the presentation. -/
private theorem algebraMap_eq_comp (p : PolynomialPresentation (algebraMap R A)) :
    algebraMap R A = p.toRingHom.comp (algebraMap R p.Poly) := by
  show algebraMap R A = p.toRingHom.comp MvPolynomial.C
  exact p.commutes.symm

/-- **The relative dualizing complex is a perfect object of `D(P)`**, for `P` the polynomial
algebra of the presentation and `A` perfect over `P`.

This is the source's identification: `ω^•_{A/R} = φ^!(R)` is a shift of the derived coextension
`RHom_P(A, R ⊗_R^L P) = RHom_P(A, P)` along the presentation's surjection
(`Dualizing.PolynomialPresentation.derivedExtensionUnitIso`), restricted to `P` that coextension
is the internal derived Hom of [stacks 0A63] out of `A` over `P`
(`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`), and that is perfect because `A` is,
by `Dualizing.isPerfect_modelHom_single_self`. -/
theorem relativeDualizingComplex_restrictScalars_isPerfect
    (p : PolynomialPresentation (algebraMap R A))
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    StacksDraft.Perfect.IsPerfect
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let : Module p.Poly A := Module.compHom A p.toRingHom
  set U := ModuleCat.restrictScalars.{u} p.toRingHom
  set Punit := (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
    (ModuleCat.of p.Poly p.Poly)
  set H := (derivedHom.{u, 0, u} p.toRingHom).obj Punit
  -- `A` placed in degree zero and read in `D(P)` is perfect.
  have hAP : StacksDraft.Perfect.IsPerfect
      (U.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :=
    isPerfect_of_iso ((U.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)) hperf
  -- Restricted to `P`, the derived coextension is the internal derived Hom out of `A`.
  have hH : StacksDraft.Perfect.IsPerfect (U.mapDerivedCategory.obj H) :=
    isPerfect_of_iso (nonempty_modelHomIsoRestrictScalarsDerivedHom p.toRingHom Punit).some.symm
      (isPerfect_modelHom_single_self _ hAP)
  -- Unwind `φ^!` at the base ring and move the shift outside the restriction.
  exact isPerfect_of_iso p.restrictScalarsUpperShriekIsoShift
    (isPerfect_shift (U.mapDerivedCategory.obj H) (p.variableCount : ℤ) hH)

/-- **A finite projective representative of the relative dualizing complex over `P`, in a tracked
window.**  Let `R → A` be of finite type, presented by `p` in `n` variables, and suppose `A`
placed in degree zero and read in `D(P)` is pseudo-coherent and of Tor amplitude in `[a, b]` over
`P`.  Then `ω^•_{A/R} = φ^!(R)`, read in `D(P)`, is represented by a complex of finite projective
`P`-modules concentrated in `[-b - n, -a - n]`.

This refines `Dualizing.PolynomialPresentation.relativeDualizingComplex_restrictScalars_isPerfect`
along the same route: `ω^•_{A/R}` is the `n`-fold shift of the derived coextension `RHom_P(A, P)`
by `Dualizing.PolynomialPresentation.derivedExtensionUnitIso`, restricted to `P` that coextension
is the internal derived Hom out of `A` over `P`
(`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`), and that Hom has a finite projective
representative in `[-b, -a]` by
`Dualizing.exists_finiteProjectiveRepresentative_modelHom_single_self`; the shift moves the window
down by `n`. -/
theorem relativeDualizingComplex_restrictScalars_exists_finiteProjectiveRepresentative
    (p : PolynomialPresentation (algebraMap R A)) (a b : ℤ)
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))))
    (hamp : StacksDraft.Perfect.HasFlatRepresentative.{u, u}
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) a b) :
    ∃ H : CochainComplex (ModuleCat.{u} p.Poly) ℤ,
      (∀ i : ℤ, Module.Finite p.Poly (H.X i) ∧ Module.Projective p.Poly (H.X i)) ∧
        H.IsStrictlyGE (-b - (p.variableCount : ℤ)) ∧
          H.IsStrictlyLE (-a - (p.variableCount : ℤ)) ∧
            Nonempty ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
                (p.upperShriekFunctor.{u, 0}.obj
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                    (ModuleCat.of R R))) ≅ DerivedCategory.Q.obj H) := by
  set U := ModuleCat.restrictScalars.{u} p.toRingHom
  set Punit := (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
    (ModuleCat.of p.Poly p.Poly)
  set H := (derivedHom.{u, 0, u} p.toRingHom).obj Punit
  set n : ℤ := (p.variableCount : ℤ)
  obtain ⟨H₀, hfp, hGE, hLE, ⟨e₀⟩⟩ :=
    exists_finiteProjectiveRepresentative_modelHom_single_self
      (U.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) a b hpc hamp
  exact ⟨H₀⟦n⟧, fun i => hfp _, H₀.isStrictlyGE_shift (-b) n (-b - n) (by omega),
    H₀.isStrictlyLE_shift (-a) n (-a - n) (by omega),
    ⟨p.restrictScalarsUpperShriekIsoShift ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} p.Poly)) n).mapIso
        ((nonempty_modelHomIsoRestrictScalarsDerivedHom p.toRingHom Punit).some.symm ≪≫ e₀) ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app H₀⟩⟩

/-- **Tor amplitude of the relative dualizing complex over the base, in a tracked window.**  Let
`R → A` be of finite type, presented by `p` in `n` variables, and suppose `A` placed in degree
zero and read in `D(P)` is pseudo-coherent and of Tor amplitude in `[a, b]` over `P`.  Then
`ω^•_{A/R} = φ^!(R)` has Tor amplitude in `[-b - n, -a - n]` as a complex of `R`-modules.

The finite projective representative over `P` of
`relativeDualizingComplex_restrictScalars_exists_finiteProjectiveRepresentative` restricts along
the flat — indeed free — `R → P` to a complex of flat `R`-modules in the same window, which by
[stacks 0654] is Tor amplitude in that window.  This refines
`relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectModule`, which records the same
conclusion with the window existentially quantified. -/
@[sga "5 III 6.2" "partial"]
theorem relativeDualizingComplex_hasTorAmplitude
    (p : PolynomialPresentation (algebraMap R A)) (a b : ℤ)
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))))
    (hamp : StacksDraft.Perfect.HasFlatRepresentative.{u, u}
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
      (-b - (p.variableCount : ℤ)) (-a - (p.variableCount : ℤ)) := by
  obtain ⟨H, hfp, hGE, hLE, ⟨e⟩⟩ :=
    p.relativeDualizingComplex_restrictScalars_exists_finiteProjectiveRepresentative a b hpc hamp
  exact (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) _ _ _).2
    (StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso
      (restrictScalarsDerivedCompIsoOfEq _ _ _ p.algebraMap_eq_comp _).symm
      (hasFlatRepresentative_restrictScalars_of_projectiveRepresentative _ _ _ H
        (fun i => (hfp i).2) hGE hLE e Module.Flat.of_free))

/-- **[stacks 0BZW] (1)(b)**, with the perfectness hypothesis in the form that the route consumes:
the relative dualizing complex `ω^•_{A/R} = φ^!(R)` of a homomorphism of finite type presented by
`p` has finite Tor dimension as a complex of `R`-modules, provided `A` is a perfect module over the
polynomial algebra `P` of the presentation — which by [stacks 068Y] is exactly perfectness of `φ`.

The form of Tag 0BZW itself, with `φ` a perfect ring map, is
`relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap`.

`ω^•_{A/R}` is perfect in `D(P)` by
`Dualizing.PolynomialPresentation.relativeDualizingComplex_restrictScalars_isPerfect`, and `P` is
free over `R`, so a bounded finite projective representative over `P` restricts to a bounded flat
representative over `R`; by [stacks 0654] that is finite Tor dimension. -/
@[sga "5 III 6.2" "partial"]
theorem relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectModule
    (p : PolynomialPresentation (algebraMap R A))
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    StacksDraft.TorAmplitude.HasFiniteTorDimension
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  exact hasFiniteTorDimension_of_iso_restrictScalars_of_isPerfect _ _
    (p.relativeDualizingComplex_restrictScalars_isPerfect hperf) Module.Flat.of_free
    (restrictScalarsDerivedCompIsoOfEq _ _ _ p.algebraMap_eq_comp _)

/-- **[Stacks, Tag 0BZW] (1)(b).**  Let `φ : R →+* A` be a perfect homomorphism of finite type of
Noetherian rings, presented by `p`.  Then the relative dualizing complex `ω^•_{A/R} = φ^!(R)` has
finite Tor dimension as a complex of `R`-modules.

Perfectness of `φ` is perfectness of `A` over the polynomial algebra of any presentation
([stacks 068Y], `RingHom.isPerfectModule_of_isPerfectRingMap`), and that is the hypothesis of
`relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectModule`.

Perfectness of `φ` is `RingHom.IsPerfectRingMap`, which carries the derived tensor product it is
stated with, as in [stacks 0BZK]; finite Tor dimension over `R` is read at the canonical
certified derived tensor product, which is the one the definition of relative perfection
([stacks 0DHS]) is written with. -/
@[stacks 0BZW "(1)(b)", sga "5 III 6.2" "partial"]
theorem relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap
    (p : PolynomialPresentation (algebraMap R A))
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived) :
    StacksDraft.TorAmplitude.HasFiniteTorDimension
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
  p.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectModule
    (RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived hf
      p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective)

/-- **[Stacks, Tag 0BZW] (1)(b), under the flatness hypothesis of (2).**  For a flat homomorphism
of finite type of Noetherian rings, `ω^•_{A/R} = φ^!(R)` has finite Tor dimension as a complex of
`R`-modules.

Over a Noetherian ring finite type is finite presentation, so a flat `φ` is a perfect ring map by
[stacks 067J]; that discharges the hypothesis `hf` of
`relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap`, together with the derived
tensor product it is stated with, for which the canonical certified tensoring of the base is taken.
Finite type of `φ` is not a hypothesis: a polynomial presentation exists only for a map of finite
type, so `p` supplies it. -/
@[sga "5 III 6.2" "partial"]
theorem relativeDualizingComplex_hasFiniteTorDimension_of_flat
    [IsNoetherianRing R] (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat) :
    StacksDraft.TorAmplitude.HasFiniteTorDimension
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R
  exact p.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap
    D.tensor D.comparison D.isLeftDerived
    ((RingHom.isPerfectRingMap_of_flat_of_finitePresentation R A).2 D.tensor D.comparison
      D.isLeftDerived)

/-- **[Stacks, Tag 0BZW] (2)(a).**  Let `φ : R → A` be a flat homomorphism of finite type of
Noetherian rings, presented by `p`.  Then `ω^•_{A/R} = φ^!(R)` is perfect relative to `R` in the
sense of [stacks 0DHS].

Nothing is carried.  Relative perfection is by definition the conjunction of pseudo-coherence over
`A` and finite Tor dimension over `R`: the first is [stacks 0BZW] (1)(a), available as
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isPseudoCoherent_of_flat`, and the
second is [stacks 0BZW] (1)(b), which is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_hasFiniteTorDimension_of_flat` above.

This is the same statement as
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect_of_flat` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativePerfection`, which reaches it by the
fibrewise criterion [stacks 0GHJ] and therefore carries the open projection-formula compatibility
`Dualizing.PolynomialPresentation.ProjectionCompatibility` at every residue field of `R`.  Here
nothing is carried; both are kept, the two routes being independent. -/
@[stacks 0BZW "(2)(a)"]
theorem relativeDualizingComplex_isRelativelyPerfect
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  exact ⟨p.relativeDualizingComplex_isPseudoCoherent_of_flat hflat,
    p.relativeDualizingComplex_hasFiniteTorDimension_of_flat hflat⟩

end PolynomialPresentation

end Dualizing

end

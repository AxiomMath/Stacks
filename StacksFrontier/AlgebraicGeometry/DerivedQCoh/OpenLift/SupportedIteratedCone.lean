module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ScalarTorsionSupport
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ShiftedSummandLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenSubspaceBaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QcqsPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SectionIdealSumCapture
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.CategoryTheory.Triangulated.IteratedScalarCone
public import Mathlib.CategoryTheory.Shift.Linear
import StacksCore.Tactic.StacksAttribute

/-!
# An iterated cone on a perfect complex over an affine scheme, supported on a closed set

Let `A` be a commutative ring, `X = Spec A`, let `U ⊆ X` be a quasi-compact open and let `T ⊆ X`
be a closed set with quasi-compact complement.  Let `F` be a perfect object of `D(𝒪_U)` whose
cohomology is supported on `T ∩ U`.

This file carries out steps 1 to 4 of the proof of [Stacks, Tag 08EK]: it produces a *perfect*
object `C` of `D(𝒪_X)` whose cohomology is supported on `T` and whose restriction to `U` has `F`
as a direct summand.

* `T` is cut out by finitely many global functions `g_1, …, g_s`
  (`AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_of_isRetrocompact_compl`).
* A power of each `g_j` kills the identity of `F`, because `F` is supported on `T ∩ U` and `U` is
  quasi-compact and quasi-separated ([Stacks, Tag 08EJ]).
* `F ⊕ F[1]` is the restriction of a perfect object `E₀` of `D(𝒪_X)` ([Stacks, Tag 08EI]).
* Coning off a power of each `g_j` in turn on `E₀` gives `C`, with `F` still a summand of `C|_U`
  and a power of each `g_j` killing the identity of `C`
  (`Stacks.Triangulated.exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso`); the latter
  puts the cohomology of `C` on `V(g_1, …, g_s) = T`
  (`Stacks.DerivedQCoh.cohomologySupportedOn_zeroLocus_of_smul_id_eq_zero`).

What [Stacks, Tag 08EK] still needs after this is its steps 5 and 6: [Stacks, Tag 08EH] applied
to the endomorphism of `C|_U` that is the identity on the complement of `F` and zero on `F`, and
the observation that the perfect object `I ⊗^L C` it produces is still supported on `T`.

## Main results

* `Stacks.DerivedQCoh.OpenLift.shiftFunctor_derivedCategory_linear`: the shift on the derived
  category of modules on a scheme is linear over a base ring acting through the global sections.
* `Stacks.DerivedQCoh.OpenLift.isTriangulated_derivedRestrict`: restriction along an open
  immersion is a triangulated functor on unbounded derived categories.
* `Stacks.DerivedQCoh.OpenLift.smul_eq_smul_comp`: a scalar acting through a composite ring map
  acts as its image acts.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_iteratedCone_biprod_summand`: the iterated cone
  over `Spec A`, with perfectness as the preserved property.
* `Stacks.DerivedQCoh.OpenLift.exists_pow_smul_id_eq_zero_of_isPerfect`: **[Stacks, Tag 08EJ]**
  applied on `U` to the identity of `F`, in the form a power of a global function of `X` kills
  the identity of `F`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_cohomologySupportedOn_biprod_summand`: steps 1
  to 4 of [Stacks, Tag 08EK].

## Implementation notes

**The three bridges this file crosses.**  The chain [Stacks, Tag 08EG]–[Stacks, Tag 08EI] is
stated for `Stacks.Cohomology.PerfectComplexes.IsPerfect` on
`StrictlyPerfect.OXMod (Spec A).toRingedSpace` and for
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, while the support condition of
[Stacks, Tag 08DA] and the scalar-torsion criterion
`Stacks.DerivedQCoh.cohomologySupportedOn_zeroLocus_of_smul_id_eq_zero` are stated for
`AlgebraicGeometry.Scheme.Modules` and `Stacks.Duality.OpenImmersion.derivedRestrict`.  Objects and
morphisms pass between the two spellings, but instance search does not.

*The restriction functor.*  Everything below is written with
`Stacks.Duality.OpenImmersion.derivedRestrict U.ι`, the spelling the support condition uses; the
conclusion of [Stacks, Tag 08EI] is carried across by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.  Its
`CategoryTheory.Functor.IsTriangulated` is not an instance -- the exactness instances that
`CategoryTheory.Functor.mapDerivedCategory` is built from are lemmas for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` -- and is supplied by
`isTriangulated_derivedRestrict`.

*Perfectness as a predicate.*  The iteration
`Stacks.Triangulated.exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso`
is applied with its predicate still a *variable*, and only then specialized to
`Stacks.Cohomology.PerfectComplexes.IsPerfect`.  Supplying the predicate directly makes the
elaborator unify `DerivedCategory (Spec A).Modules` with the `OXMod` spelling while the
instances of the former are still being synthesized, and `CategoryTheory.Preadditive` is then
not found.

*The base ring.*  The scalars are kept in `Γ(X, 𝒪_X)` on both sides of the restriction, with the
ring map into `Γ(U, 𝒪_U)` changing instead -- the arrangement
`Stacks.DerivedQCoh.derivedRestrict_linear` is stated in.  [Stacks, Tag 08EJ] on `U` is stated
with its scalars in `Γ(U, 𝒪_U)`, and `smul_eq_smul_comp` -- which is `rfl`, both linear
structures being `CategoryTheory.Linear.ofRingMorphism` of a composite -- is what reads it back
with scalars in `Γ(X, 𝒪_X)`.

**The generators are a `List`.**  A finitely generated ideal gives a `Finset` of generators, and
`Finset.toList` turns it into the list the iteration consumes; nothing needs the generators to be
distinct.

## References

* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Lemma 36.13.9 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 36.13.8 (Tag 08EI)](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.Cohomology.PerfectComplexes

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Instances and spelling bridges -/

/-- **The shift on `D(𝒪_X)` is `B`-linear**, for a ring map from `B` to the global sections of
`𝒪_X`.  The shift is the functor induced on the localization by the shift of cochain complexes,
which is `B`-linear degreewise, and `CategoryTheory.Shift.linear_of_localization` descends
that. -/
theorem shiftFunctor_derivedCategory_linear (X : Scheme.{u}) (B : Type u) [CommRing B]
    (φ : B →+* Γ(X, ⊤)) (n : ℤ) :
    letI : Linear B X.Modules := Scheme.linearOfRingHom X B φ
    (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) n).Linear B := by
  let : Linear B X.Modules := Scheme.linearOfRingHom X B φ
  exact CategoryTheory.Shift.linear_of_localization _
    (DerivedCategory.Q (C := X.Modules))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) n

/-- **Restriction along an open immersion is a triangulated functor on unbounded derived
categories.**  It is the functor induced by an exact functor, which factors through the homotopy
category; `CategoryTheory.Functor.isTriangulated_of_precomp_iso` at that factorization is the
statement. -/
theorem isTriangulated_derivedRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (derivedRestrict f).IsTriangulated :=
  CategoryTheory.Functor.isTriangulated_of_precomp_iso
    (Scheme.Modules.restrictFunctor f).mapDerivedCategoryFactorsh

/-- **A scalar acting through a composite ring map acts as its image acts.**  Both linear
structures are `CategoryTheory.Linear.ofRingMorphism` of a ring map into the centre of the
category of modules, composed with the given ring maps, so the two scalar actions are the same
morphism. -/
theorem smul_eq_smul_comp (X : Scheme.{u}) {B B' : Type u} [CommRing B] [CommRing B']
    (φ : B →+* B') (ψ : B' →+* Γ(X, ⊤)) :
    letI : Linear B X.Modules := Scheme.linearOfRingHom X B (ψ.comp φ)
    letI : Linear B' X.Modules := Scheme.linearOfRingHom X B' ψ
    ∀ {M N : DerivedCategory X.Modules} (b : B) (g : M ⟶ N), b • g = φ b • g :=
  fun _ _ => rfl

/-! ### The iterated cone over an affine scheme -/

variable {A : CommRingCat.{u}}

/-- **The iterated cone of [Stacks, Tag 08EK] over `Spec A`.**  Let `U ⊆ Spec A` be an open, `F`
an object of `D(𝒪_U)` on whose identity a power of each member of a list `l` of global functions
acts as zero, and `E₀` a perfect object of `D(𝒪_{Spec A})` with `F ⊞ F⟦1⟧ ≅ E₀|_U`.  Then there
are a perfect object `E` of `D(𝒪_{Spec A})` on whose identity a power of each member of `l` acts
as zero, and an object `S` of `D(𝒪_U)` with `S ⊞ F ≅ E|_U`.

This is `Stacks.Triangulated.exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso` at
`C = D(𝒪_{Spec A})`, `D = D(𝒪_U)` and `R` the restriction, with perfectness as the predicate
preserved by cones -- [Stacks, Tag 08CR]. -/
theorem exists_isPerfect_iteratedCone_biprod_summand (U : (Spec A).Opens)
    (l : List Γ(Spec A, ⊤)) (F : DerivedCategory U.toScheme.Modules)
    (E₀ : DerivedCategory (Spec A).Modules)
    (hE₀ : IsPerfect (X := (Spec A).toRingedSpace) E₀)
    (e₀ : F ⊞ F⟦(1 : ℤ)⟧ ≅ (derivedRestrict U.ι).obj E₀)
    (hl : letI : Linear Γ(Spec A, ⊤) U.toScheme.Modules :=
            Scheme.linearOfRingHom U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom
          ∀ a ∈ l, ∃ m : ℕ, a ^ m • 𝟙 F = 0) :
    letI : Linear Γ(Spec A, ⊤) (Spec A).Modules :=
      Scheme.linearOfRingHom (Spec A) Γ(Spec A, ⊤) (RingHom.id Γ(Spec A, ⊤))
    ∃ (E : DerivedCategory (Spec A).Modules) (S : DerivedCategory U.toScheme.Modules),
      IsPerfect (X := (Spec A).toRingedSpace) E ∧
      (∀ a ∈ l, ∃ k : ℕ, a ^ k • 𝟙 E = 0) ∧
      Nonempty (S ⊞ F ≅ (derivedRestrict U.ι).obj E) := by
  let : Linear Γ(Spec A, ⊤) (Spec A).Modules :=
    Scheme.linearOfRingHom (Spec A) Γ(Spec A, ⊤) (RingHom.id Γ(Spec A, ⊤))
  let : Linear Γ(Spec A, ⊤) U.toScheme.Modules :=
    Scheme.linearOfRingHom U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor
      (DerivedCategory (Spec A).Modules) n).Linear Γ(Spec A, ⊤) := fun n =>
    shiftFunctor_derivedCategory_linear (Spec A) Γ(Spec A, ⊤) (RingHom.id Γ(Spec A, ⊤)) n
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor
      (DerivedCategory U.toScheme.Modules) n).Linear Γ(Spec A, ⊤) := fun n =>
    shiftFunctor_derivedCategory_linear U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom n
  let : Functor.Linear Γ(Spec A, ⊤) (derivedRestrict U.ι) :=
    derivedRestrict_linear U.ι (RingHom.id Γ(Spec A, ⊤))
  let : (derivedRestrict U.ι).IsTriangulated := isTriangulated_derivedRestrict U.ι
  have H : ∀ (P : DerivedCategory (Spec A).Modules → Prop),
      (∀ T : Triangle (DerivedCategory (Spec A).Modules),
        T ∈ distTriang (DerivedCategory (Spec A).Modules) → P T.obj₁ → P T.obj₂ → P T.obj₃) →
      P E₀ →
      ∃ (E : DerivedCategory (Spec A).Modules) (S : DerivedCategory U.toScheme.Modules),
        P E ∧ (∀ a ∈ l, ∃ k : ℕ, a ^ k • 𝟙 E = 0) ∧
        Nonempty (S ⊞ F ≅ (derivedRestrict U.ι).obj E) := fun P hP hP₀ =>
    Stacks.Triangulated.exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso P hP
      (derivedRestrict U.ι) F l E₀ hP₀ e₀ hl
  exact H _ (fun T hT h1 h2 =>
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      (X := (Spec A).toRingedSpace) T hT h1 h2) hE₀

/-! ### Step 1: a power of each generator kills the identity -/

/-- **A global function of `Spec A` vanishing on the support of a perfect object of `D(𝒪_U)` has
a power killing its identity.**  This is [Stacks, Tag 08EJ] applied on `U` -- a quasi-compact
open of an affine scheme, hence quasi-compact and quasi-separated -- to the identity of `F`,
with the scalar read in `Γ(Spec A, 𝒪)` rather than in `Γ(U, 𝒪)`.

The restriction of `g` to `U` is the scalar [Stacks, Tag 08EJ] produces a power of, and
`smul_eq_smul_comp` identifies its action with the action of `g` itself; the two differ only in
which ring map the linear structure is taken at. -/
theorem exists_pow_smul_id_eq_zero_of_isPerfect (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F) (g : Γ(Spec A, ⊤))
    (hsupp : CohomologySupportedOn U.toScheme.ringCatSheaf
      ((U.toScheme.basicOpen ((U.ι.appTop).hom g) : Set U.toScheme)ᶜ) F) :
    letI : Linear Γ(Spec A, ⊤) U.toScheme.Modules :=
      Scheme.linearOfRingHom U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom
    ∃ m : ℕ, g ^ m • 𝟙 F = 0 := by
  let : Linear Γ(Spec A, ⊤) U.toScheme.Modules :=
    Scheme.linearOfRingHom U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := U.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨m, hm⟩ :=
    Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn_qcqs
      ((U.ι.appTop).hom g) F F hF
      (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect
        U.toScheme F hF)
      (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect
        U.toScheme F hF)
      hsupp (𝟙 F)
  refine ⟨m, ?_⟩
  rw [smul_eq_smul_comp U.toScheme (U.ι.appTop).hom (RingHom.id Γ(U.toScheme, ⊤)) (g ^ m) (𝟙 F),
    map_pow]
  exact hm

/-! ### Steps 1 to 4 of [Stacks, Tag 08EK] -/

/-- **Steps 1 to 4 of [Stacks, Tag 08EK].**  Let `A` be a commutative ring, `X = Spec A`, let
`T ⊆ X` be closed with quasi-compact complement, let `U ⊆ X` be a quasi-compact open, and let
`F` be a perfect object of `D(𝒪_U)` whose cohomology is supported on `T ∩ U`.  Then there are a
perfect object `E` of `D(𝒪_X)` whose cohomology is supported on `T` and an object `S` of
`D(𝒪_U)` with `S ⊞ F ≅ E|_U`.

`T` is the zero locus of finitely many global functions `g_1, …, g_s`; a power of each kills the
identity of `F`, since `F` is supported on `T ∩ U ⊆ V(g_j) ∩ U`; `F ⊕ F[1]` is the restriction
of a perfect object by [Stacks, Tag 08EI]; coning off a power of each `g_j` in turn keeps `F` a
summand of the restriction and makes a power of each `g_j` kill the identity of the result, which
puts its cohomology on `V(g_1, …, g_s) = T`. -/
theorem exists_isPerfect_cohomologySupportedOn_biprod_summand (T : Set (Spec A))
    (hT : IsClosed T) (hTc : IsCompact (Tᶜ : Set (Spec A))) (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F)
    (hFT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) F) :
    ∃ (E : DerivedCategory (Spec A).Modules) (S : DerivedCategory U.toScheme.Modules),
      IsPerfect (X := (Spec A).toRingedSpace) E ∧
      CohomologySupportedOn (Spec A).ringCatSheaf T E ∧
      Nonempty (S ⊞ F ≅ (derivedRestrict U.ι).obj E) := by
  classical
  obtain ⟨I, hIFG, hI⟩ :=
    AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_of_isRetrocompact_compl (Spec A) T hT
      (hTc.isRetrocompact hT.isOpen_compl)
  obtain ⟨t, ht⟩ := hIFG
  have hzero : (Spec A).zeroLocus (U := ⊤) (t : Set Γ(Spec A, ⊤)) = T := by
    rw [← (Spec A).zeroLocus_span (U := ⊤) (t : Set Γ(Spec A, ⊤)), ht]
    exact hI
  -- a power of each generator kills the identity of `F`
  have hkill : letI : Linear Γ(Spec A, ⊤) U.toScheme.Modules :=
        Scheme.linearOfRingHom U.toScheme Γ(Spec A, ⊤) (U.ι.appTop).hom
      ∀ g ∈ t.toList, ∃ m : ℕ, g ^ m • 𝟙 F = 0 := by
    intro g hg
    refine exists_pow_smul_id_eq_zero_of_isPerfect U hU F hF g ?_
    refine Stacks.DerivedQCoh.cohomologySupportedOn_mono_standard ?_ hFT
    intro x hx
    have hxT : x.1 ∈ T := hx
    have hgx : x.1 ∉ (Spec A).basicOpen g := by
      rw [← hzero] at hxT
      exact ((Spec A).mem_zeroLocus_iff _ _).1 hxT g (Finset.mem_toList.1 hg)
    have hmem : (x ∈ U.ι ⁻¹ᵁ ((Spec A).basicOpen g)) ↔
        (x.1 ∈ (Spec A).basicOpen g) := Iff.rfl
    have hpre : U.ι ⁻¹ᵁ ((Spec A).basicOpen g) =
        U.toScheme.basicOpen ((U.ι.appTop).hom g) := Scheme.preimage_basicOpen_top U.ι g
    intro hc
    rw [← hpre] at hc
    exact hgx (hmem.1 hc)
  -- `F ⊕ F[1]` is the restriction of a perfect object
  obtain ⟨E₀, hE₀, ⟨e⟩⟩ := exists_isPerfect_biprod_shift_iso_restrict_toScheme U hU F hF
  -- the iterated cone
  obtain ⟨E, S, hEperf, hEkill, hES⟩ :=
    exists_isPerfect_iteratedCone_biprod_summand U t.toList F E₀ hE₀
      (e ≪≫ (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor
        (Spec A) U).app E₀) hkill
  refine ⟨E, S, hEperf, ?_, hES⟩
  rw [← hzero]
  refine Stacks.DerivedQCoh.cohomologySupportedOn_zeroLocus_of_smul_id_eq_zero
    (t : Set Γ(Spec A, ⊤)) E fun g hg => ?_
  exact hEkill g (Finset.mem_toList.2 hg)

end Stacks.DerivedQCoh.OpenLift

end

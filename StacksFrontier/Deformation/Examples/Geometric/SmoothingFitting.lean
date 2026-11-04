module

public import StacksFrontier.RingTheory.Fitting.Basic
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Fitting.Rank
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Deformation.Examples.Geometric.CurveChartGeometry
public import StacksFrontier.Deformation.Examples.Geometric.CurveStalkComparison
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.RelativeDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.JacobsonClosedPoints
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.Criteria
public import Mathlib.RingTheory.RingHom.EssFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fitting ideals of modules of differentials

Fitting ideals of modules of differentials commute with base change ([Stacks, Tag 07ZA]), with
ring isomorphisms and with localization; at a smooth point of a scheme of dimension at most one
over a field the first Fitting ideal of the differentials of the local ring is the unit ideal; and
a Fitting clause on the local rings of a scheme over `Spec A` gives the same clause on its affine
opens. The file also records the structure maps, the complete intersection property and the
dimension of the local rings of such schemes.

## Main results

* `Deformation.Examples.Smoothing.fittingIdeal_kaehler_of_isPushout`: base change.
* `Deformation.Examples.Smoothing.fittingIdeal_kaehler_of_ringEquiv`: transport along ring
  isomorphisms of the algebra and of the base.
* `Deformation.Examples.Smoothing.fittingIdeal_kaehler_of_isLocalization`: localization.
* `Deformation.Examples.Smoothing.eq_top_of_sup_eq_top_of_le_maximalIdeal`: an ideal of a
  local ring which is the unit ideal modulo a non-unit ideal is the unit ideal.
* `Deformation.Examples.Smoothing.fittingIdeal_kaehler_stalk_eq_top_of_mem_smoothLocus`: at
  a smooth point of a scheme of dimension at most one over a field, the first Fitting ideal of the
  differentials of the local ring is the unit ideal.
* `Deformation.Examples.Smoothing.appLE_mem_fittingIdeal_relativeDifferentials_of_forall_stalk`:
  the Fitting clause on affine opens from the Fitting clause on local rings.
* `Deformation.Examples.Smoothing.algebraMap_stalkAlgebra_comp_specMap` and
  `Deformation.Examples.Smoothing.stalkAlgebraOver_eq_stalkAlgebra`: the structure maps of local
  rings over the base.
* `Deformation.Examples.Smoothing.isCompleteIntersectionLocalRing_stalk`: the local rings of
  a local complete intersection over `k` are complete intersections.
* `Deformation.Examples.Smoothing.ringKrullDim_stalk_le_one_and_trdeg_eq_zero`: dimension
  and residue transcendence degree at a closed point of a curve.

## References

* [The Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [The Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public noncomputable section

open TensorProduct AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Deformation.Examples.Smoothing

/-- **Fitting ideals of differentials commute with base change.** For a pushout square
`C' = R' ⊗[R] C`, the `d`-th Fitting ideal of `Ω_{C'/R'}` is the extension of that of
`Ω_{C/R}`. -/
theorem fittingIdeal_kaehler_of_isPushout {R C R' C' : Type u} [CommRing R] [CommRing C]
    [CommRing R'] [CommRing C'] [Algebra R C] [Algebra R R'] [Algebra R C'] [Algebra C C']
    [Algebra R' C'] [IsScalarTower R C C'] [IsScalarTower R R' C'] [Algebra.IsPushout R R' C C']
    [Module.Finite C Ω[C⁄R]] (d : ℕ) :
    letI : Module.Finite C' Ω[C'⁄R'] :=
      Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv R R' C C')
    fittingIdeal (R := C') (M := Ω[C'⁄R']) (d : ℤ) =
      (fittingIdeal (R := C) (M := Ω[C⁄R]) (d : ℤ)).map (algebraMap C C') := by
  let : Module.Finite C' Ω[C'⁄R'] :=
    Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv R R' C C')
  rw [← fittingIdeal_eq_of_linearEquiv (KaehlerDifferential.tensorKaehlerEquiv R R' C C') d]
  exact (fittingIdeal_basic_properties.{u, u, u, u} (R := C) (M := Ω[C⁄R])).2.2.1 C' d

/-- **Fitting ideals of differentials commute with localization of the algebra.** For a
localization `Cₘ` of an `R`-algebra `C`, the `d`-th Fitting ideal of `Ω_{Cₘ/R}` is the extension
of that of `Ω_{C/R}`. -/
theorem fittingIdeal_kaehler_of_isLocalization {R C Cₘ : Type u} [CommRing R] [CommRing C]
    [CommRing Cₘ] [Algebra R C] [Algebra C Cₘ] [Algebra R Cₘ] [IsScalarTower R C Cₘ]
    (M : Submonoid C) [IsLocalization M Cₘ] [Module.Finite C Ω[C⁄R]] (d : ℕ) :
    letI : Module.Finite Cₘ Ω[Cₘ⁄R] :=
      Module.Finite.of_isLocalizedModule M (KaehlerDifferential.map R R C Cₘ)
    fittingIdeal (R := Cₘ) (M := Ω[Cₘ⁄R]) (d : ℤ) =
      (fittingIdeal (R := C) (M := Ω[C⁄R]) (d : ℤ)).map (algebraMap C Cₘ) := by
  have hloc : IsLocalizedModule M (KaehlerDifferential.map R R C Cₘ) :=
    omega_localization_total R C M Cₘ
  let : Module.Finite Cₘ Ω[Cₘ⁄R] :=
    Module.Finite.of_isLocalizedModule M (KaehlerDifferential.map R R C Cₘ)
  have hbc : IsBaseChange Cₘ (KaehlerDifferential.map R R C Cₘ) :=
    (isLocalizedModule_iff_isBaseChange M Cₘ (KaehlerDifferential.map R R C Cₘ)).mp hloc
  rw [← fittingIdeal_eq_of_linearEquiv hbc.equiv d]
  exact (fittingIdeal_basic_properties.{u, u, u, u} (R := C) (M := Ω[C⁄R])).2.2.1 Cₘ d

/-- In a local ring, an ideal which is the unit ideal modulo an ideal contained in the
maximal ideal is the unit ideal. -/
theorem eq_top_of_sup_eq_top_of_le_maximalIdeal {C : Type*} [CommRing C] [IsLocalRing C]
    {I J : Ideal C} (hI : I ≤ IsLocalRing.maximalIdeal C) (hJI : J ⊔ I = ⊤) : J = ⊤ := by
  by_contra hJ
  exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top
    (top_le_iff.mp (hJI ▸ sup_le (IsLocalRing.le_maximalIdeal hJ) hI))

/-- In a local ring, an ideal whose image modulo an ideal contained in
the maximal ideal is the unit ideal is the unit ideal. -/
theorem eq_top_of_map_quotient_eq_top {C : Type*} [CommRing C] [IsLocalRing C]
    {I J : Ideal C} (hI : I ≤ IsLocalRing.maximalIdeal C)
    (hJ : J.map (Ideal.Quotient.mk I) = ⊤) : J = ⊤ := by
  refine eq_top_of_sup_eq_top_of_le_maximalIdeal hI ?_
  have h := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J
  rwa [hJ, Ideal.comap_top, Ideal.mk_ker, eq_comm] at h

/-- Along a bijective change of the base, the differentials stay finite and their Fitting ideals
do not change. -/
private theorem fittingIdeal_kaehler_eq_of_bijective {R R' C : Type u} [CommRing R] [CommRing R']
    [CommRing C] [Algebra R C] [Algebra R R'] [Algebra R' C] [IsScalarTower R R' C]
    (hρ : Function.Bijective (algebraMap R R')) [Module.Finite C Ω[C⁄R]] :
    ∃ _ : Module.Finite C Ω[C⁄R'], ∀ d : ℕ,
      fittingIdeal (R := C) (M := Ω[C⁄R']) (d : ℤ) = fittingIdeal (R := C) (M := Ω[C⁄R]) (d : ℤ) :=
  have : Algebra.IsPushout R R' C C :=
    (Algebra.IsPushout.of_bijective_left (R := R) (A := R') (T := C) hρ).symm
  ⟨Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv R R' C C), fun d => by
    rw [fittingIdeal_kaehler_of_isPushout (R := R) (C := C) (R' := R') (C' := C) d,
      Algebra.algebraMap_self, Ideal.map_id]⟩

/-- **Fitting ideals of differentials are transported along ring isomorphisms.** Let
`ψ : C ≃+* C'` and `ρ : R ≃+* R'` be ring isomorphisms compatible with the structure maps
`R → C` and `R' → C'`. Then the `d`-th Fitting ideal of `Ω_{C'/R'}` is the image under `ψ` of
that of `Ω_{C/R}`. -/
theorem fittingIdeal_kaehler_of_ringEquiv {R C R' C' : Type u} [CommRing R] [CommRing C]
    [CommRing R'] [CommRing C'] [Algebra R C] [Algebra R' C'] (ψ : C ≃+* C') (ρ : R ≃+* R')
    (h : ∀ r : R, algebraMap R' C' (ρ r) = ψ (algebraMap R C r))
    [Module.Finite C Ω[C⁄R]] [Module.Finite C' Ω[C'⁄R']] (d : ℕ) :
    fittingIdeal (R := C') (M := Ω[C'⁄R']) (d : ℤ) =
      (fittingIdeal (R := C) (M := Ω[C⁄R]) (d : ℤ)).map ψ := by
  let : Algebra C C' := ψ.toRingHom.toAlgebra
  let : Algebra R C' := (ψ.toRingHom.comp (algebraMap R C)).toAlgebra
  have : IsScalarTower R C C' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (IsUnit.submonoid C) C' :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit
      ψ.bijective
  have hloc := fittingIdeal_kaehler_of_isLocalization (R := R) (C := C) (Cₘ := C')
    (IsUnit.submonoid C) d
  let : Module.Finite C' Ω[C'⁄R] :=
    Module.Finite.of_isLocalizedModule (IsUnit.submonoid C) (KaehlerDifferential.map R R C C')
  let : Algebra R R' := ρ.toRingHom.toAlgebra
  have : IsScalarTower R R' C' := IsScalarTower.of_algebraMap_eq fun r => (h r).symm
  obtain ⟨_, hbase⟩ :=
    fittingIdeal_kaehler_eq_of_bijective (R := R) (R' := R') (C := C') ρ.bijective
  rw [hbase d, hloc]
  rfl

section Stalk

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Through `Deformation.Examples.stalkAlgebraOver`, the germ map from the sections over an affine
open is `k`-linear. -/
theorem isScalarTower_sections_stalkAlgebraOver {U : X.Opens} (_hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) :
    letI := sectionsAlgebra f U
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  let := sectionsAlgebra f U
  let : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show (f.stalkMap x) (StructureSheaf.toStalk k (f.base x) a) =
    X.presheaf.germ U x hx ((f.appLE ⊤ U _) ((Scheme.ΓSpecIso (.of k)).inv a))
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial
    ((Scheme.ΓSpecIso (.of k)).inv a))
  rfl

/-- The differentials of a local ring of a scheme locally of finite type over `k` form a finite
module, for the `k`-algebra structure `Deformation.Examples.stalkAlgebraOver`. -/
theorem moduleFinite_kaehler_stalkAlgebraOver [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  let := sectionsAlgebra f U
  have := finiteType_sectionsAlgebra f hU
  let : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := isScalarTower_sections_stalkAlgebraOver f hU x hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact Module.Finite.of_isLocalizedModule (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk x))

/-- At a smooth point of a scheme of dimension at most one over `k`, the first Fitting ideal of
the differentials of the local ring is the unit ideal. -/
theorem fittingIdeal_kaehler_stalk_eq_top_of_mem_smoothLocus [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ∈ f.smoothLocus) :
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    letI := moduleFinite_kaehler_stalkAlgebraOver f x
    fittingIdeal (R := X.presheaf.stalk x) (M := Ω[X.presheaf.stalk x⁄k]) (1 : ℤ) = ⊤ := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  let := sectionsAlgebra f U
  have := finiteType_sectionsAlgebra f hU
  let : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := isScalarTower_sections_stalkAlgebraOver f hU x hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let P : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hsm : Algebra.IsSmoothAt k P.asIdeal := isSmoothAt_primeIdealOf f hU ⟨x, hxU⟩ hx
  have hloc : localKrullDim (PrimeSpectrum Γ(X, U)) P ≤ 1 := by
    rw [← topologicalKrullDimAt_eq_localKrullDim]
    calc topologicalKrullDimAt (PrimeSpectrum Γ(X, U)) P
        ≤ topologicalKrullDim (PrimeSpectrum Γ(X, U)) := by
          unfold topologicalKrullDimAt
          let W : {W : Set (PrimeSpectrum Γ(X, U)) // P ∈ W ∧ IsOpen W} :=
            ⟨Set.univ, ⟨Set.mem_univ _, isOpen_univ⟩⟩
          calc _ ≤ topologicalKrullDim (↥W.1) := iInf_le _ W
            _ = _ := IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
      _ = topologicalKrullDim U := (IsHomeomorph.topologicalKrullDim_eq _
          hU.isoSpec.hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le X (U : Set X)
      _ ≤ 1 := hdim
  have hrank : Module.finrank P.asIdeal.ResidueField
      (P.asIdeal.ResidueField ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) ≤ 1 := by
    have h := ((Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
      (k := k) P (Localization.AtPrime P.asIdeal)).1.out 1 2).mp hsm
    exact_mod_cast h.trans hloc
  have hnot : ¬ fittingIdeal (R := Γ(X, U)) (M := Ω[Γ(X, U)⁄k]) ((1 : ℕ) : ℤ) ≤ P.asIdeal :=
    ((fittingIdeal_local_generation_tfae (R := Γ(X, U)) (M := Ω[Γ(X, U)⁄k]) 1
      P.asIdeal).out 1 2).mpr hrank
  have h := fittingIdeal_kaehler_of_isLocalization (R := k) (C := Γ(X, U))
    (Cₘ := X.presheaf.stalk x) P.asIdeal.primeCompl 1
  rw [Nat.cast_one] at h hnot
  rw [h]
  exact IsLocalization.AtPrime.map_eq_top_of_not_le (X.presheaf.stalk x) hnot

end Stalk

section SpecBase

variable (A : Type u) [CommRing A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A))

/-- The `A`-algebra structure on a local ring of a scheme over `Spec A`, through the global
sections: `A ≅ Γ(Spec A, ⊤) → Γ(Y, ⊤) → 𝒪_{Y,y}`. -/
abbrev stalkAlgebra (y : Y) : Algebra A (Y.presheaf.stalk y) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom.toAlgebra

/-- The structure map of `Deformation.Examples.Smoothing.stalkAlgebra` factors through the germ
map of any open neighbourhood. -/
theorem appTop_germ_eq_appLE_germ {U : Y.Opens} (y : Y) (hy : y ∈ U) :
    g.appTop ≫ Y.presheaf.germ ⊤ y (by simp) =
      g.appLE ⊤ U (by simp) ≫ Y.presheaf.germ U y hy := by
  rw [← Y.presheaf.germ_res (homOfLE le_top) y hy]
  rfl

/-- The Fitting ideals of `Ω_{𝒪_{Y,y}/A}` are those of `Ω_{𝒪_{Y,y}/Γ(Spec A, ⊤)}`, and the latter
are the localizations of those of `Ω_{Γ(Y, U)/Γ(Spec A, ⊤)}` on an affine neighbourhood `U`. The
module of differentials of the local ring is finite. -/
@[sga "7 VI 5.3" "(2), special case"]
theorem moduleFinite_kaehler_stalkAlgebra_and_fittingIdeal_eq [LocallyOfFiniteType g]
    (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := stalkAlgebra A g y
    letI := Stacks.Smooth.algebraAppLE g (SmoothingCriterion.le_preimage_top g U.1)
    letI := moduleFinite_kaehlerDifferential_appLE g U.2 (isAffineOpen_top _)
      (SmoothingCriterion.le_preimage_top g U.1)
    ∃ _ : Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄A], ∀ d : ℕ,
      fittingIdeal (R := Y.presheaf.stalk y) (M := Ω[Y.presheaf.stalk y⁄A]) (d : ℤ) =
        (fittingIdeal (R := Γ(Y, U.1)) (M := Ω[Γ(Y, U.1)⁄Γ(Spec (.of A), ⊤)]) (d : ℤ)).map
          (Y.presheaf.germ U.1 y hy).hom := by
  let := stalkAlgebra A g y
  let := Stacks.Smooth.algebraAppLE g (SmoothingCriterion.le_preimage_top g U.1)
  have := moduleFinite_kaehlerDifferential_appLE g U.2 (isAffineOpen_top _)
    (SmoothingCriterion.le_preimage_top g U.1)
  let K := Γ(Spec (.of A), ⊤)
  let : Algebra Γ(Y, U.1) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  let : Algebra K (Y.presheaf.stalk y) :=
    (g.appLE ⊤ U.1 (SmoothingCriterion.le_preimage_top g U.1) ≫
      Y.presheaf.germ U.1 y hy).hom.toAlgebra
  have : IsScalarTower K Γ(Y, U.1) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  have := U.2.isLocalization_stalk ⟨y, hy⟩
  have hloc := fittingIdeal_kaehler_of_isLocalization (R := K) (C := Γ(Y, U.1))
    (Cₘ := Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  let : Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄K] :=
    Module.Finite.of_isLocalizedModule (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (KaehlerDifferential.map K K Γ(Y, U.1) (Y.presheaf.stalk y))
  let ρ : K ≃+* A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  let : Algebra K A := ρ.toRingHom.toAlgebra
  have : IsScalarTower K A (Y.presheaf.stalk y) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show ((g.appLE ⊤ U.1 _ ≫ Y.presheaf.germ U.1 y hy)).hom r =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom
        ((Scheme.ΓSpecIso (.of A)).hom r)
    rw [appTop_germ_eq_appLE_germ A g y hy, ← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]
  obtain ⟨hfin, hbase⟩ := fittingIdeal_kaehler_eq_of_bijective (R := K) (R' := A)
    (C := Y.presheaf.stalk y) ρ.bijective
  exact ⟨hfin, fun d => (hbase d).trans (hloc d)⟩

/-- The differentials of a local ring of a scheme locally of finite type over `Spec A` form a
finite module over it, for `Deformation.Examples.Smoothing.stalkAlgebra`. -/
theorem moduleFinite_kaehler_stalkAlgebra [LocallyOfFiniteType g] (y : Y) :
    letI := stalkAlgebra A g y
    Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄A] := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) (by simp)
  exact (moduleFinite_kaehler_stalkAlgebra_and_fittingIdeal_eq A g ⟨U, hU⟩ y hyU).1

/-- **The Fitting clause on affine opens from the Fitting clause on local rings.** Let
`g : Y ⟶ Spec A` be locally of finite type, `a ∈ A` and `d : ℕ`. If at every point `y` the image
of `a` in `𝒪_{Y,y}` lies in the `d`-th Fitting ideal of `Ω_{𝒪_{Y,y}/A}`, then over every affine
open `U` the image of `a` in `Γ(Y, U)` lies in the sections of the `d`-th Fitting ideal sheaf of
`Ω_{Y/Spec A}`. -/
theorem appLE_mem_fittingIdeal_relativeDifferentials_of_forall_stalk [LocallyOfFiniteType g]
    (a : A) (d : ℕ)
    (h : ∀ y : Y,
      letI := stalkAlgebra A g y
      letI := moduleFinite_kaehler_stalkAlgebra A g y
      algebraMap A (Y.presheaf.stalk y) a ∈
        fittingIdeal (R := Y.presheaf.stalk y) (M := Ω[Y.presheaf.stalk y⁄A]) (d : ℤ))
    (U : Y.affineOpens) :
    g.appLE ⊤ U.1 (SmoothingCriterion.le_preimage_top g U.1) ((Scheme.ΓSpecIso (.of A)).inv a) ∈
      (AlgebraicGeometry.fittingIdeal (Scheme.Hom.relativeDifferentials g) (d : ℤ)).ideal U := by
  refine U.2.mem_ideal_iff.mpr fun y hy => ?_
  let := stalkAlgebra A g y
  obtain ⟨hfin, hfit⟩ := moduleFinite_kaehler_stalkAlgebra_and_fittingIdeal_eq A g U y hy
  have hst := stalk_fittingIdeal_relativeDifferentials g (d : ℤ) y U hy (isAffineOpen_top _)
    (SmoothingCriterion.le_preimage_top g U.1)
  rw [← IdealSheafData.stalk_eq_map_germ _ y U hy, hst, ← hfit d]
  have hy' := h y
  have hga : (Y.presheaf.germ U.1 y hy).hom
      ((g.appLE ⊤ U.1 (SmoothingCriterion.le_preimage_top g U.1))
        ((Scheme.ΓSpecIso (.of A)).inv a)) =
      algebraMap A (Y.presheaf.stalk y) a := by
    show _ = ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom a
    rw [appTop_germ_eq_appLE_germ A g y hy]
    rfl
  rw [hga]
  exact hy'

/-- A local ring of a scheme locally of finite type over `Spec A` is essentially of finite type
over `A`, for `Deformation.Examples.Smoothing.stalkAlgebra`. -/
theorem essFiniteType_stalk [LocallyOfFiniteType g] (y : Y) :
    letI := stalkAlgebra A g y
    Algebra.EssFiniteType A (Y.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) (by simp)
  have h1 : (g.appLE ⊤ U (by simp)).hom.FiniteType :=
    g.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  let := (Y.presheaf.germ U y hyU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  have hg : (Y.presheaf.germ U y hyU).hom.EssFiniteType :=
    Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
  have h := (h1.comp h0).essFiniteType.comp hg
  let := stalkAlgebra A g y
  rw [← RingHom.essFiniteType_algebraMap]
  convert h using 1
  show ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [appTop_germ_eq_appLE_germ A g y hyU]
  rfl

end SpecBase

section LocalRings

/-- **The structure map of `Deformation.Examples.Smoothing.stalkAlgebra` along a change of
base.** For `f : Y ⟶ Spec L` and `ψ : A →+* L`, the `A`-algebra structure of a local ring of `Y`
over `Spec A` sends `a` to the image under the stalk map of `f` of `ψ a` in the local ring of
`Spec L`. -/
theorem algebraMap_stalkAlgebra_comp_specMap {L A : Type u} [CommRing L] [CommRing A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of L)) (ψ : A →+* L) (y : Y) (a : A) :
    letI := stalkAlgebra A (f ≫ Spec.map (CommRingCat.ofHom ψ)) y
    letI : Algebra L ((Spec (.of L)).presheaf.stalk (f.base y)) :=
      StructureSheaf.stalkAlgebra L (f.base y)
    algebraMap A (Y.presheaf.stalk y) a =
      (f.stalkMap y).hom (algebraMap L ((Spec (.of L)).presheaf.stalk (f.base y)) (ψ a)) := by
  have hnat := congrArg (fun φ => φ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  show (Y.presheaf.germ ⊤ y _) ((f ≫ Spec.map (CommRingCat.ofHom ψ)).appTop
    ((Scheme.ΓSpecIso (.of A)).inv a)) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← hnat]
  refine (Scheme.Hom.germ_stalkMap_apply f ⊤ y trivial _).symm.trans ?_
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The two `k`-algebra structures on a local ring of a scheme over `Spec k`,
`Deformation.Examples.stalkAlgebraOver` and `Deformation.Examples.Smoothing.stalkAlgebra`, are
equal. -/
theorem stalkAlgebraOver_eq_stalkAlgebra (x : X) :
    (stalkAlgebraOver (Over.mk f) x : Algebra k (X.presheaf.stalk x)) = stalkAlgebra k f x := by
  refine Algebra.algebra_ext _ _ fun a => ?_
  show (f.stalkMap x) (StructureSheaf.toStalk k (f.base x) a) =
    (X.presheaf.germ ⊤ x _) (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial
    ((Scheme.ΓSpecIso (.of k)).inv a))
  rfl

/-- **A local ring of a local complete intersection over `k` is a complete intersection over `k`,
essentially of finite type over `k`** ([Stacks, Tag 01UG]), for the `k`-algebra structure
`Deformation.Examples.stalkAlgebraOver`. -/
theorem isCompleteIntersectionLocalRing_stalk [LocallyOfFiniteType f]
    (hf : IsLocalCompleteIntersectionOverField f) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    IsCompleteIntersectionLocalRing k (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  rw [stalkAlgebraOver_eq_stalkAlgebra f x]
  let := stalkAlgebra k f x
  have h3 := ((localCompleteIntersection_tfae k X f).out 1 3).mp hf
  dsimp only at h3
  exact ⟨(Stacks.SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection
    k _).mpr (h3 x), essFiniteType_stalk k f x⟩

/-- **At a closed point of a scheme of dimension at most one, locally of finite type over
`k`, the local ring has dimension at most one and the residue field is algebraic over `k`.** The
second assertion is [Stacks, Tag 0478], for the `k`-algebra structure
`Deformation.Examples.stalkAlgebraOver`. -/
theorem ringKrullDim_stalk_le_one_and_trdeg_eq_zero [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.presheaf.stalk x) := stalkAlgebraOver (Over.mk f) x
    ringKrullDim (X.presheaf.stalk x) ≤ 1 ∧
      Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = 0 := by
  refine ⟨(Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
    X x).trans hdim, ?_⟩
  rw [stalkAlgebraOver_eq_stalkAlgebra f x]
  let := stalkAlgebra k f x
  have h := isAlgebraic_residueField_of_isClosed f hx
  have halg : (inferInstance : Algebra k
      (IsLocalRing.ResidueField (X.presheaf.stalk x))) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have : @Algebra.IsAlgebraic k (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _
      inferInstance := by
    rw [halg]; exact h
  exact trdeg_eq_zero

end LocalRings

end Deformation.Examples.Smoothing

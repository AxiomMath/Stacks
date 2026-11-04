module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FlatFibers
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The discriminant of a finite locally free morphism

Let `f : X ⟶ Y` be a finite locally free morphism of schemes. Over an affine open `V` of `Y` the
inverse image `f ⁻¹ᵁ V` is affine and `Γ(X, f ⁻¹ᵁ V)` is a finite projective
`Γ(Y, V)`-algebra, so it has a discriminant ideal in the sense of
`Stacks.Discriminant.algebraDiscriminantIdeal`. Those ideals are compatible with restriction to
principal opens, and the resulting ideal sheaf on `Y` is the *discriminant* of `f`. It is locally
principal, its support is the image of the ramification locus of `f`, and it is the unit ideal
sheaf exactly when `f` is étale.

## Main definitions

* `Stacks.Discriminant.discriminantIdeal` is the discriminant ideal sheaf of a finite locally
  free morphism.
* `Stacks.Discriminant.discriminant` is the closed subscheme it cuts out.

## Main results

* `Stacks.Discriminant.discriminantIdeal_properties` is Tag 0BJF: the discriminant ideal sheaf is
  locally principal, its support consists of the images of the ramified points, and it equals the
  unit ideal sheaf exactly when the morphism is étale.
* `Stacks.Discriminant.discriminantIdeal_isLocallyPrincipal`,
  `Stacks.Discriminant.mem_discriminantIdeal_support_iff` and
  `Stacks.Discriminant.etale_iff_discriminantIdeal_eq_top` are its three clauses.

## Implementation notes

The commutative algebra is already available in
`StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal`; what is added here is the
globalisation. Three points are worth recording.

Local principality is *not* obtained by trivialising the module of sections on the given affine
open — a finite projective module need not be free — but by shrinking to a principal open of it,
using `Stacks.Discriminant.exists_away_free_at_prime` to find one on which the module becomes
free, and `Stacks.Discriminant.free_of_localized_free` to recognise the sections over that
principal open as the localisation.

The support computation needs no base-change statement for the unramified locus and no étale
criterion for the restricted morphism. The non-unramified locus of `f` is closed because
`AlgebraicGeometry.UnramifiedAt` is witnessed by an affine chart that works for every point of
itself (`AlgebraicGeometry.isOpen_setOf_unramifiedAt`), and `f` is a closed map, so a point
outside the image of that locus has an affine neighbourhood `V` over which every point of `X` is
unramified. `AlgebraicGeometry.etale_sections_of_unramifiedAt` turns that directly into
étaleness of `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)`, which is what the discriminant ideal is computed from.

The converse direction, that a unit discriminant ideal forces étaleness, is where the fibres
enter: `Stacks.Discriminant.algebraDiscriminantIdeal_eq_top_iff_surjective` makes the trace form
of every residue-field fibre nondegenerate, hence that fibre étale, and
`AlgebraicGeometry.etale_of_flat_of_fibers_finite_separable` assembles the fibres.

`Stacks.Discriminant.discriminantIdeal` does not use its
`Stacks.Morphisms.IsFiniteLocallyFree` instance argument:
`Stacks.Discriminant.algebraDiscriminantIdeal` is defined for an arbitrary algebra, taking the
value `⊥` where finite projectivity fails, so the family of affine ideals makes sense for any
morphism. The argument is kept because every statement
about the ideal sheaf needs it, and because the definition is the source's, which is only given
for a finite locally free morphism; the environment linter's report of an unused argument is
therefore expected.

## References

* [Stacks Project, Tag 0BJF](https://stacks.math.columbia.edu/tag/0BJF)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

/-- The ideal sheaf defining the discriminant of a finite locally free morphism. -/
@[ega "IV 18.2.7"]
def discriminantIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] : Y.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    algebraDiscriminantIdeal Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)

/-- The discriminant closed subscheme of a finite locally free morphism. -/
abbrev discriminant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] : Scheme.{u} :=
  (discriminantIdeal f).subscheme

section Sections

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- Over an affine open of the target, the sections of a finite locally free morphism form a
finite projective algebra. -/
private theorem affineSections_finite_projective (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) ∧
      Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := by
  have hV := IsAffineHom.isAffine_preimage (f := f) U.1 U.2
  let R := Γ(Y, U.1)
  let A := Γ(X, f ⁻¹ᵁ U.1)
  let : Algebra R A := (f.app U.1).hom.toAlgebra
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  have : Module.Finite R A := RingHom.finite_algebraMap.mp (f.finite_app U.1 U.2)
  have : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.mp <| by
    rw [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.appLE_eq_app]
    exact f.finitePresentation_appLE U.2 hV le_rfl
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp <| by
    rw [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.appLE_eq_app]
    exact f.flat_appLE U.2 hV le_rfl
  have : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- The sections of a finite locally free morphism over an affine open of the target are flat and
of finite presentation. -/
private theorem affineSections_flat_finitePresentation (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) :=
      (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    Module.Flat Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) ∧
      Algebra.FinitePresentation Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := by
  have hV := IsAffineHom.isAffine_preimage (f := f) U.1 U.2
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) :=
    (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  obtain ⟨-, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  exact ⟨RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 hV le_rfl),
    RingHom.finitePresentation_algebraMap.mp (f.finitePresentation_appLE U.2 hV le_rfl)⟩

end Sections

section Compatibility

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- The sections of a finite locally free morphism over a principal affine open of the target are
free whenever the corresponding localisation of the module of sections is. -/
private theorem affinePreimage_basicOpen_free (V : Y.affineOpens) (a : Γ(Y, V.1))
    (hfree : letI : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
      Module.Free (Localization.Away a) (LocalizedModule.Away a (Γ(X, f ⁻¹ᵁ V.1)))) :
    letI : Algebra (Γ(Y, Y.basicOpen a)) (Γ(X, X.basicOpen (f.app V.1 a))) :=
      (f.appLE (Y.basicOpen a) (X.basicOpen (f.app V.1 a))
        (by rw [Scheme.preimage_basicOpen])).hom.toAlgebra
    Module.Free (Γ(Y, Y.basicOpen a)) (Γ(X, X.basicOpen (f.app V.1 a))) := by
  classical
  let R := Γ(Y, V.1)
  let A := Γ(X, f ⁻¹ᵁ V.1)
  let R' := Γ(Y, Y.basicOpen a)
  let b := f.app V.1 a
  let A' := Γ(X, X.basicOpen b)
  have hU := IsAffineHom.isAffine_preimage (f := f) V.1 V.2
  let : Algebra R A := (f.app V.1).hom.toAlgebra
  let : Algebra R R' := (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom.toAlgebra
  have : IsLocalization (.powers a) R' := V.2.isLocalization_basicOpen a
  let : Algebra A A' := (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom.toAlgebra
  let : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let : Algebra R' A' := (f.appLE (Y.basicOpen a) (X.basicOpen b)
    (by rw [Scheme.preimage_basicOpen])).hom.toAlgebra
  have : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (by
      let iY := (homOfLE (Y.basicOpen_le a)).op
      let iX := (homOfLE (X.basicOpen_le b)).op
      have hX : f.app V.1 ≫ X.presheaf.map iX =
          f.appLE V.1 (X.basicOpen b) (X.basicOpen_le b) := by
        rw [f.app_eq_appLE, f.appLE_map]
      have hY : Y.presheaf.map iY ≫
          f.appLE (Y.basicOpen a) (X.basicOpen b) (by rw [Scheme.preimage_basicOpen]) =
          f.appLE V.1 (X.basicOpen b) (X.basicOpen_le b) := by
        rw [f.map_appLE]
      have h := congrArg CommRingCat.Hom.hom (hX.trans hY.symm)
      simpa only [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using h)
  have : IsLocalization.Away (algebraMap R A a) A' := hU.isLocalization_basicOpen b
  exact free_of_localized_free R A R' A' a hfree

end Compatibility

/-- The discriminant ideal of a finite projective algebra is compatible with localisation at one
element of the base. -/
private theorem algebraDiscriminantIdeal_map_localization
    (R A R' A' : Type*) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (a : R) [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    [Algebra R R'] [IsLocalization (.powers a) R']
    [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [IsLocalization (Algebra.algebraMapSubmonoid A (.powers a)) A']
    [Algebra R' A'] [IsScalarTower R R' A'] :
    (algebraDiscriminantIdeal R A).map (algebraMap R R') = algebraDiscriminantIdeal R' A' := by
  have : Algebra.IsPushout R A R' A' :=
    (Algebra.isLocalization_iff_isPushout (.powers a) R').mp inferInstance
  have : Algebra.IsPushout R R' A A' := Algebra.IsPushout.symm inferInstance
  let e := Algebra.IsPushout.equiv R R' A A'
  have : Module.Finite R' A' := Module.Finite.equiv e.toLinearEquiv
  have : Module.Projective R' A' := Module.Projective.of_equiv e.toLinearEquiv
  exact (algebraDiscriminantIdeal_map R A R').trans
    (algebraDiscriminantIdeal_algEquiv R' _ A' e)

/-- An open subset of a scheme that is equal to a principal open of an affine open has sections a
localisation of the sections on that affine open. -/
private theorem isLocalization_basicOpen_of_eq
    {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U))
    (hV : V = X.basicOpen a) (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsLocalization.Away a Γ(X, V) := by
  subst V
  exact hU.isLocalization_basicOpen a

section Ideal

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- The affine discriminant ideals of a finite locally free morphism are compatible with
restriction to principal opens of the target. -/
private theorem affineDiscriminantIdeal_map_basicOpen (V : Y.affineOpens) (a : Γ(Y, V.1)) :
    letI : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
    letI : Algebra Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
      (f.app (Y.basicOpen a)).hom.toAlgebra
    (algebraDiscriminantIdeal Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)).map
        (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom =
      algebraDiscriminantIdeal Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) := by
  let R := Γ(Y, V.1)
  let A := Γ(X, f ⁻¹ᵁ V.1)
  let R' := Γ(Y, Y.basicOpen a)
  let A' := Γ(X, f ⁻¹ᵁ Y.basicOpen a)
  let : Algebra R A := (f.app V.1).hom.toAlgebra
  have : Module.Finite R A := (affineSections_finite_projective f V).1
  have : Module.Projective R A := (affineSections_finite_projective f V).2
  let : Algebra R R' := (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom.toAlgebra
  have : IsLocalization (.powers a) R' := V.2.isLocalization_basicOpen a
  let : Algebra A A' :=
    (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map
      (homOfLE (Y.basicOpen_le a))).op).hom.toAlgebra
  let : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R' A' := (f.app (Y.basicOpen a)).hom.toAlgebra
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (f.naturality (homOfLE (Y.basicOpen_le a)).op)).symm
  have hU := IsAffineHom.isAffine_preimage (f := f) V.1 V.2
  have : IsLocalization.Away (algebraMap R A a) A' :=
    isLocalization_basicOpen_of_eq hU (f.app V.1 a) (f.preimage_basicOpen a) _
  exact algebraDiscriminantIdeal_map_localization R A R' A' a

/-- On an affine open of the target, the discriminant ideal sheaf is the discriminant ideal of
the algebra of sections. -/
@[sga "1 I 4.10" "discriminant ideal sheaf"]
theorem discriminantIdeal_ideal (V : Y.affineOpens) :
    letI : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
    (discriminantIdeal f).ideal V = algebraDiscriminantIdeal Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := by
  let I : Y.IdealSheafData :=
    { ideal := fun U ↦
        let := (f.app U.1).hom.toAlgebra
        algebraDiscriminantIdeal Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      map_ideal_basicOpen := affineDiscriminantIdeal_map_basicOpen f }
  exact congrArg (fun J : Y.IdealSheafData ↦ J.ideal V)
    (Scheme.IdealSheafData.ofIdeals_ideal I)

end Ideal

/-- An ideal sheaf assembled from a family of affine ideals is the unit ideal sheaf exactly when
every member of the family is. -/
private theorem idealSheafData_ofIdeals_eq_top_iff
    {Y : Scheme.{u}} (I : ∀ U : Y.affineOpens, Ideal Γ(Y, U)) :
    Scheme.IdealSheafData.ofIdeals I = ⊤ ↔ ∀ U, I U = ⊤ := by
  refine ⟨fun h U ↦ ?_, fun h ↦ ?_⟩
  · simpa [h] using Scheme.IdealSheafData.ideal_ofIdeals_le I U
  · refine top_unique ((Scheme.IdealSheafData.le_ofIdeals_iff ..).2 fun U ↦ ?_)
    rw [h U]
    rfl

section Main

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- The discriminant ideal sheaf is the unit ideal sheaf exactly when every affine discriminant
ideal is the unit ideal. -/
private theorem discriminantIdeal_eq_top_iff_affineSections :
    discriminantIdeal f = ⊤ ↔ ∀ U : Y.affineOpens,
      letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
      algebraDiscriminantIdeal Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
  unfold discriminantIdeal
  rw [idealSheafData_ofIdeals_eq_top_iff]

/-- An étale finite locally free morphism has unit discriminant ideal on every affine open of the
target. -/
@[sga "1 I 4.10" "partial"]
private theorem algebraDiscriminantIdeal_eq_top_of_etale_affineSections [Etale f]
    (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) →
      Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) →
        algebraDiscriminantIdeal Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
  intro hfinite hprojective
  let V := f ⁻¹ᵁ U.1
  let : Algebra Γ(Y, U.1) Γ(X, V) := (f.app U.1).hom.toAlgebra
  have hring : (algebraMap Γ(Y, U.1) Γ(X, V)).Etale := by
    rw [RingHom.algebraMap_toAlgebra]
    simpa only [Scheme.Hom.appLE_eq_app] using
      f.etale_appLE U.2 (IsAffineHom.isAffine_preimage U.1 U.2) le_rfl
  exact algebraDiscriminantIdeal_eq_top_of_etale Γ(Y, U.1) Γ(X, V)
    (RingHom.etale_algebraMap.mp hring)

end Main

/-- A unit discriminant ideal makes the trace form of every residue-field fibre nondegenerate,
hence that fibre étale. -/
@[sga "1 I 4.10" "special case"]
private theorem etale_scalarTensor_of_algebraDiscriminantIdeal_eq_top
    (R : Type u) (A : Type v) (K : Type w)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    [Module.Projective R A] [Field K] [Algebra R K]
    (h : algebraDiscriminantIdeal R A = ⊤) : Algebra.Etale K (K ⊗[R] A) := by
  have hsurj := (algebraDiscriminantIdeal_eq_top_iff_surjective R A).mp h
  exact (finiteDimensional_etale_iff_traceForm_nondegenerate K (K ⊗[R] A)).2
    (traceForm_scalarTensor_nondegenerate_of_surjective R A K hsurj)

/-- A finite projective algebra with unit discriminant ideal is étale. -/
private theorem etale_of_algebraDiscriminantIdeal_eq_top
    (R : Type u) (A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A]
    (h : algebraDiscriminantIdeal R A = ⊤) : Algebra.Etale R A := by
  classical
  let g : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : LocallyOfFinitePresentation g := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hg : Etale g := by
    apply etale_of_flat_of_fibers_finite_separable
    intro (p : PrimeSpectrum R)
    let K := p.asIdeal.ResidueField
    have hEtaleScheme : Etale (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr
        (etale_scalarTensor_of_algebraDiscriminantIdeal_eq_top R A K h))
    have hEtaleFiber : Etale (g.fiberToSpecResidueField p) := by
      have : MorphismProperty.RespectsIso (@Etale) := by
        rw [HasRingHomProperty.eq_affineLocally (P := @Etale)]
        exact AlgebraicGeometry.affineLocally_respectsIso
          (P := RingHom.Etale) RingHom.Etale.respectsIso
      exact (MorphismProperty.arrow_mk_iso_iff (P := @Etale)
        (Spec.fiberToSpecResidueFieldIso R A p)).mpr hEtaleScheme
    let e := Spec.stalkIso (.of R) p
    have : IsLocalRing ((Spec (.of R)).presheaf.stalk p) :=
      e.commRingCatIsoToRingEquiv.symm.isLocalRing
    exact (etale_iff_iso_coproduct_spectra_finite_separable
      (IsLocalRing.ResidueField ((Spec (.of R)).presheaf.stalk p))
      (g.fiberToSpecResidueField p)).mp hEtaleFiber
  exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hg)

section Assembly

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- Over an affine open where the discriminant ideal is the unit ideal, the algebra of sections of
a finite locally free morphism is étale. -/
private theorem algebra_etale_of_discriminantIdeal_eq_top (V : Y.affineOpens)
    (h : (discriminantIdeal f).ideal V = ⊤) :
    letI : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
    Algebra.Etale Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  obtain ⟨_, _⟩ := affineSections_finite_projective f V
  rw [discriminantIdeal_ideal] at h
  exact etale_of_algebraDiscriminantIdeal_eq_top Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) h

/-- A finite locally free morphism is étale exactly when its discriminant ideal sheaf is the unit
ideal sheaf. -/
private theorem etale_iff_discriminantIdeal_eq_top_scheme :
    Etale f ↔ discriminantIdeal f = ⊤ := by
  refine ⟨fun hf ↦ ?_, fun htop ↦ ?_⟩
  · rw [discriminantIdeal_eq_top_iff_affineSections]
    intro U
    have hfp := affineSections_finite_projective f U
    exact algebraDiscriminantIdeal_eq_top_of_etale_affineSections f U hfp.1 hfp.2
  · refine (etale_iff_forall_etaleAt f).2 fun x ↦ ?_
    let V₀ := (Y.affineCover.f (Y.affineCover.idx (f x))).opensRange
    have hV₀ : IsAffineOpen V₀ := isAffineOpen_opensRange _
    have hxV : f x ∈ V₀ := Y.affineCover.covers (f x)
    let V : Y.affineOpens := ⟨V₀, hV₀⟩
    let U : X.Opens := f ⁻¹ᵁ V.1
    have hU : IsAffineOpen U := IsAffineHom.isAffine_preimage V.1 V.2
    let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
    have hEtAlg : Algebra.Etale Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) :=
      algebra_etale_of_discriminantIdeal_eq_top f V (by simp [htop])
    have hEtRing : (f.appLE V.1 U le_rfl).hom.Etale := by
      simpa [U, V, Scheme.Hom.appLE, RingHom.algebraMap_toAlgebra] using
        RingHom.etale_algebraMap.mpr hEtAlg
    exact ⟨U, hU, hxV, V.1, V.2, le_rfl, hEtRing⟩

/-- The discriminant ideal sheaf of a finite locally free morphism is locally principal. -/
@[ega "IV 18.2.7" "partial"]
private theorem discriminantIdeal_locallyPrincipal :
    Stacks.Divisors.IsLocallyPrincipal (discriminantIdeal f) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (affineSections_finite_projective f ⟨V, hV⟩).1
  have : Module.Projective Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    (affineSections_finite_projective f ⟨V, hV⟩).2
  obtain ⟨a, ha, hfree⟩ := exists_away_free_at_prime Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
    (hV.primeIdealOf ⟨y, hyV⟩)
  have hya : y ∈ Y.basicOpen a := by
    rw [← hV.fromSpec_image_basicOpen]
    exact ⟨hV.primeIdealOf ⟨y, hyV⟩, ha, hV.fromSpec_primeIdealOf ⟨y, hyV⟩⟩
  refine ⟨⟨Y.basicOpen a, hV.basicOpen a⟩, hya, ?_⟩
  rw [discriminantIdeal_ideal]
  let : Algebra Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
    (f.app (Y.basicOpen a)).hom.toAlgebra
  have : Module.Finite Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
    (affineSections_finite_projective f ⟨_, hV.basicOpen a⟩).1
  have : Module.Projective Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
    (affineSections_finite_projective f ⟨_, hV.basicOpen a⟩).2
  have : Nontrivial Γ(Y, Y.basicOpen a) :=
    ((hV.basicOpen a).primeIdealOf ⟨y, hya⟩).nontrivial
  have : Module.Free Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) := by
    have h := affinePreimage_basicOpen_free f ⟨V, hV⟩ a hfree
    have hh := (f.appLE_congr le_rfl rfl (f.preimage_basicOpen a)
      (fun {R S} g ↦ let := g.hom.toAlgebra; Module.Free R S)).mpr h
    rwa [Scheme.Hom.appLE_eq_app] at hh
  exact algebraDiscriminantIdeal_isPrincipal_of_free _ _

end Assembly

/-- An ideal sheaf whose support misses an affine open is the unit ideal there. -/
private theorem ideal_eq_top_of_disjoint_support {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (V : Y.affineOpens) (h : ∀ y ∈ V.1, y ∉ I.support) :
    I.ideal V = ⊤ := by
  refine PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.eq_empty_iff_forall_notMem.mpr ?_)
  intro p hp
  have hm : V.2.fromSpec p ∈ Y.zeroLocus (U := V.1) (I.ideal V : Set Γ(Y, V.1)) ∩ V.1 := by
    rw [← V.2.fromSpec_image_zeroLocus]
    exact ⟨p, hp, rfl⟩
  exact h _ hm.2 ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hm.2).mpr hm.1)

section Support

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]

/-- A point over an affine open with unit discriminant ideal is a point of unramifiedness. -/
private theorem unramifiedAt_of_discriminantIdeal_eq_top_on_affine (V : Y.affineOpens)
    (h : (discriminantIdeal f).ideal V = ⊤) (x : X) (hx : f x ∈ V.1) : UnramifiedAt f x := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  have := algebra_etale_of_discriminantIdeal_eq_top f V h
  refine ⟨f ⁻¹ᵁ V.1, IsAffineHom.isAffine_preimage V.1 V.2, hx, V.1, V.2, le_rfl, ?_⟩
  rw [Scheme.Hom.appLE_eq_app]
  exact ⟨inferInstance, inferInstance⟩

/-- If every point of the source over an affine open of the target is a point of unramifiedness,
then the discriminant ideal is the unit ideal on that affine open. -/
private theorem discriminantIdeal_eq_top_of_unramifiedAt (V : Y.affineOpens)
    (h : ∀ x : X, f x ∈ V.1 → UnramifiedAt f x) : (discriminantIdeal f).ideal V = ⊤ := by
  let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  have : Module.Finite Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (affineSections_finite_projective f V).1
  have : Module.Projective Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (affineSections_finite_projective f V).2
  obtain ⟨hflat, hfp⟩ := affineSections_flat_finitePresentation f V
  have hetale := etale_sections_of_unramifiedAt f V.2
    (IsAffineHom.isAffine_preimage V.1 V.2) h hflat hfp
  rw [Scheme.Hom.appLE_eq_app] at hetale
  rw [discriminantIdeal_ideal]
  exact algebraDiscriminantIdeal_eq_top_of_etale Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) hetale

/-- The support of the discriminant ideal sheaf consists of the images of the ramified points. -/
private theorem discriminantIdeal_support_iff (y : Y) :
    y ∈ (discriminantIdeal f).support ↔ ∃ x : X, f x = y ∧ ¬ UnramifiedAt f x := by
  classical
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  refine ⟨fun hy ↦ ?_, fun ⟨x, hxy, hx⟩ ↦ ?_⟩
  · by_contra hn
    let Z : Set X := {x | ¬ UnramifiedAt f x}
    have hZ : IsClosed Z := (isOpen_setOf_unramifiedAt f).isClosed_compl
    let W : Y.Opens := ⟨(f '' Z)ᶜ, (f.isClosedMap Z hZ).isOpen_compl⟩
    have hyW : y ∈ W := by
      rintro ⟨x, hx, hxy⟩
      exact hn ⟨x, hxy, hx⟩
    obtain ⟨V, hV, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset hyW
    have htop := discriminantIdeal_eq_top_of_unramifiedAt f ⟨V, hV⟩ (by
      intro x hx
      by_contra hn'
      exact hVW hx ⟨x, hn', rfl⟩)
    have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hyV).mp hy
    rw [htop] at hz
    simp [hyV] at hz
  · by_contra hy
    let W : Y.Opens := ⟨((discriminantIdeal f).support : Set Y)ᶜ,
      (discriminantIdeal f).support.isClosed.isOpen_compl⟩
    obtain ⟨V, hV, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ W from hy)
    have htop :=
      ideal_eq_top_of_disjoint_support (discriminantIdeal f) ⟨V, hV⟩ fun z hz ↦ hVW hz
    exact hx (unramifiedAt_of_discriminantIdeal_eq_top_on_affine f ⟨V, hV⟩ htop x (hxy ▸ hyV))

/-- **Stacks Project, Tag 0BJF.** The discriminant of a finite locally free morphism is locally
principal, its support consists of the images of the ramified points, and it is the unit ideal
sheaf exactly when the morphism is étale. -/
@[stacks 0BJF "discriminant properties"]
theorem discriminantIdeal_properties :
    Stacks.Divisors.IsLocallyPrincipal (discriminantIdeal f) ∧
      (∀ y : Y, y ∈ (discriminantIdeal f).support ↔
        ∃ x : X, f x = y ∧ ¬ UnramifiedAt f x) ∧
      (Etale f ↔ discriminantIdeal f = ⊤) :=
  ⟨discriminantIdeal_locallyPrincipal f, discriminantIdeal_support_iff f,
    etale_iff_discriminantIdeal_eq_top_scheme f⟩

/-- The discriminant ideal of a finite locally free morphism is locally principal. -/
@[ega "IV 18.2.7" "partial"]
alias discriminantIdeal_isLocallyPrincipal := discriminantIdeal_locallyPrincipal

/-- A point belongs to the discriminant exactly when a ramified point lies over it. -/
alias mem_discriminantIdeal_support_iff := discriminantIdeal_support_iff

/-- **Stacks Project, Tag 0BJF.** A finite locally free morphism is étale if and only if its
discriminant is empty. -/
@[stacks 0BJF]
theorem etale_iff_discriminantIdeal_eq_top : Etale f ↔ discriminantIdeal f = ⊤ :=
  (discriminantIdeal_properties f).2.2

end Support

end Stacks.Discriminant

end

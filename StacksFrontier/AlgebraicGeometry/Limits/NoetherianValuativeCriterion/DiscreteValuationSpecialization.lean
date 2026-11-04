module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# Reaching a point in the closure over a locally Noetherian scheme

A point in the closure of the image of a finite-type morphism of schemes can be reached by the
closed point of the spectrum of a discrete valuation ring.  Its generic point may be chosen to
map to the generic point of an irreducible component of the source.

## Main definitions

* `AlgebraicGeometry.DiscreteValuationSpecialization` packages the valuation-ring diagram
  together with the choices of its generic and closed points.

## Main results

* `AlgebraicGeometry.nonempty_discreteValuationSpecialization` constructs such a diagram for a
  point in the closure of the image of a finite-type morphism into a locally Noetherian scheme.
* `AlgebraicGeometry.exists_discreteValuationSpecialization_genericPoint_specializes` constructs
  one for a specialization `f x ⤳ y`, with generic point a generization of `x`.

## Implementation notes

Equality of the fraction field with the residue field at the chosen generic point is expressed by
a ring equivalence together with the assertion that the field-valued point is the canonical
residue-field point transported along this equivalence.  This is the invariant form of choosing
`K = κ(η)`.

The construction splits on whether the image of the local ring of `Y` at `y` inside the residue
field of the chosen generic point `η` is a field.  If it is, `f η = y` already, and the required
discrete valuation ring is manufactured from the local ring of the affine line over that residue
field at the origin — so the diagram exists even though no domination is available.  If it is
not, the local subring is dominated by a discrete valuation ring inside the residue field itself
(`exists_isDiscreteValuationRing_isFractionRing_of_not_isField`), which needs the essential
finite type of the composite map from the local ring at `y` to the residue field at `η`; that is
`stalkSpecializes_residueField_essFiniteType`.

## References

* [Stacks Project, Tag 0CM2](https://stacks.math.columbia.edu/tag/0CM2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The specialization map on stalks along a specialization of points is essentially of finite
type: both stalks are localizations of the sections over one affine open containing both
points. -/
private theorem stalkSpecializes_essFiniteType {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    (X.presheaf.stalkSpecializes h).hom.EssFiniteType := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  let M := Γ(X, U)
  let A := X.presheaf.stalk y
  let B := X.presheaf.stalk x
  let : Algebra M A := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  let : Algebra M B := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime A (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have : IsLocalization.AtPrime B (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hA : (algebraMap M A).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization A
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
  have hB : (algebraMap M B).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization B
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hcomp : (X.presheaf.stalkSpecializes h).hom.comp (algebraMap M A) =
      algebraMap M B := by
    change (X.presheaf.stalkSpecializes h).hom.comp (X.presheaf.germ U y hyU).hom =
      (X.presheaf.germ U x hxU).hom
    exact congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU h)
  exact (RingHom.EssFiniteType.comp_iff hA).mp (hcomp ▸ hB)

/-- For a morphism locally of finite type, the composite of the specialization map on stalks of
the target, the stalk map and the residue map of the source is essentially of finite type. -/
private theorem stalkSpecializes_residueField_essFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X} {y : Y} (h : f x ⤳ y) :
    (Y.presheaf.stalkSpecializes h ≫ f.stalkMap x ≫ X.residue x).hom.EssFiniteType := by
  change ((X.residue x).hom.comp
    ((f.stalkMap x).hom.comp (Y.presheaf.stalkSpecializes h).hom)).EssFiniteType
  exact RingHom.EssFiniteType.comp
    (RingHom.EssFiniteType.comp (stalkSpecializes_essFiniteType h)
      (LocallyOfFiniteType.stalkMap f x))
    (RingHom.FiniteType.of_surjective _ (X.residue_surjective x)).essFiniteType

/-- The closed point of a local ring with a local map from the stalk at `y` maps to `y`. -/
private theorem base_comp_fromSpecStalk_closedPoint {Y : Scheme.{u}} {y : Y} {A : Type u}
    [CommRing A] [IsLocalRing A] (ψ : ↑(Y.presheaf.stalk y) →+* A) [IsLocalHom ψ] :
    (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y).base
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) = y := by
  change (Y.fromSpecStalk y)
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint A)) = y
  rw [Spec_closedPoint]
  exact Y.fromSpecStalk_closedPoint

/-- A valuation-ring diagram reaching `y`, whose field-valued point maps to the generic point of
an irreducible component of `X`. -/
structure DiscreteValuationSpecialization {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) where
  /-- The discrete valuation ring in the diagram. -/
  valuationRing : Type u
  /-- The fraction field in the diagram. -/
  fractionField : Type u
  [commRing : CommRing valuationRing]
  [isDomain : IsDomain valuationRing]
  [isDVR : IsDiscreteValuationRing valuationRing]
  [field : Field fractionField]
  [algebra : Algebra valuationRing fractionField]
  [isFractionRing : IsFractionRing valuationRing fractionField]
  /-- The generic point of the irreducible component selected in the source. -/
  genericPoint : X
  /-- The selected irreducible component of the source. -/
  component : Set X
  component_mem : component ∈ irreducibleComponents X
  isGenericPoint : IsGenericPoint genericPoint component
  /-- The field-valued point of `X`. -/
  toSource : Spec (CommRingCat.of fractionField) ⟶ X
  /-- The valuation-ring-valued point of `Y`. -/
  toTarget : Spec (CommRingCat.of valuationRing) ⟶ Y
  maps_genericPoint :
    toSource.base (⟨⊥, inferInstance⟩ : PrimeSpectrum fractionField) = genericPoint
  maps_closedPoint :
    toTarget.base
      (⟨IsLocalRing.maximalIdeal valuationRing, inferInstance⟩ : PrimeSpectrum valuationRing) = y
  commutes :
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap valuationRing fractionField)).op ≫
        toTarget =
      toSource ≫ f
  /-- Away from the case where the selected generic point already maps to `y`, the fraction field
  can be chosen to be the residue field of that generic point. -/
  residueFieldEquiv :
    f.base genericPoint ≠ y →
      ∃ e : fractionField ≃+* X.residueField genericPoint,
        toSource =
          Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
            X.fromSpecResidueField genericPoint

namespace DiscreteValuationSpecialization

attribute [instance] commRing isDomain isDVR field algebra isFractionRing

end DiscreteValuationSpecialization

/-- For a morphism locally of finite type into a locally Noetherian scheme, a specialization
`f x ⤳ y` is reached by a discrete valuation ring whose generic point is the generic point of an
irreducible component of the source through `x`. -/
theorem exists_discreteValuationSpecialization_genericPoint_specializes {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {x : X} {y : Y}
    (hfx : f x ⤳ y) :
    ∃ d : DiscreteValuationSpecialization f y, d.genericPoint ⤳ x := by
  let C := irreducibleComponent x
  let c : irreducibleComponents X := ⟨C, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : X := (genericPoints.ofComponent c).1
  have hη : IsGenericPoint η C := genericPoints.isGenericPoint_ofComponent c
  have hηx : η ⤳ x := hη.specializes mem_irreducibleComponent
  have hηy : f η ⤳ y := (hηx.map f.continuous).trans hfx
  let S := Y.presheaf.stalk y
  let L := X.residueField η
  let φ : ↑S →+* L := (Y.presheaf.stalkSpecializes hηy ≫ f.stalkMap η ≫ X.residue η).hom
  have hφ : φ.EssFiniteType := stalkSpecializes_residueField_essFiniteType f hηy
  let R : Subring L := φ.range
  let : IsLocalRing R := (LocalSubring.range φ).isLocalRing
  have : IsNoetherianRing (↑S) := inferInstance
  let : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv (↑S ⧸ RingHom.ker φ) (RingHom.quotientKerEquivRange φ)
  let : Algebra R L := inferInstance
  let K := FractionRing R
  let : Field K := inferInstance
  let : Algebra R K := inferInstance
  let : IsFractionRing R K := inferInstance
  have hRL : (algebraMap R L).EssFiniteType := RingHom.EssFiniteType.of_comp
    (RingHom.rangeRestrict φ) hφ
  let gRL : R →ₐ[R] L := { toRingHom := algebraMap R L, commutes' := fun _ => rfl }
  let gKL : K →ₐ[R] L := IsFractionRing.liftAlgHom
    (A := R) (K := K) (L := L) (g := gRL) (fun _ _ h => Subtype.ext h)
  let : Algebra K L := gKL.toAlgebra
  have hRK : (algebraMap R K).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  have hcomp : (algebraMap K L).comp (algebraMap R K) = algebraMap R L :=
    RingHom.ext gKL.commutes
  have hKL : (algebraMap K L).EssFiniteType :=
    (RingHom.EssFiniteType.comp_iff hRK).mp (hcomp ▸ hRL)
  let source : Spec (.of L) ⟶ X := X.fromSpecResidueField η
  let targetFromStalk : Spec (.of L) ⟶ Y :=
    Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y
  have hsourceTarget : source ≫ f = targetFromStalk := by
    dsimp [source, targetFromStalk, φ]
    rw [Scheme.fromSpecResidueField, Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hηy]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  by_cases hR : IsField R
  · let P : Ideal (Polynomial L) := Ideal.span {Polynomial.X}
    have hPX : P.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
    have hPne : P ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero
    let A := Localization.AtPrime P
    let F := FractionRing (Polynomial L)
    let : CommRing A := inferInstance
    let : IsDomain A := inferInstance
    let : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A P
    let : Algebra (Polynomial L) A := inferInstance
    let : Algebra L A := inferInstance
    let : Algebra A F := inferInstance
    let : IsFractionRing A F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A F
    have hDVR : IsDiscreteValuationRing A := by
      let : IsDedekindDomain (Polynomial L) := inferInstance
      exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (Polynomial L) hPne A
    let : IsDiscreteValuationRing A := hDVR
    have : IsLocalHom (RingHom.rangeRestrict φ) :=
      IsLocalHom.of_surjective _ (RingHom.rangeRestrict_surjective φ)
    have hker : RingHom.ker φ = IsLocalRing.maximalIdeal S := by
      calc
        RingHom.ker φ = (⊥ : Ideal R).comap (RingHom.rangeRestrict φ) := by
          ext s
          exact ⟨fun hs => Subtype.ext hs, fun hs => congrArg Subtype.val hs⟩
        _ = (IsLocalRing.maximalIdeal R).comap (RingHom.rangeRestrict φ) := by
          rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hR]
        _ = IsLocalRing.maximalIdeal S :=
          IsLocalRing.maximalIdeal_comap (RingHom.rangeRestrict φ)
    have : IsLocalHom φ := by
      apply (IsLocalRing.local_hom_TFAE φ).out 5 1 |>.mp
      simpa [RingHom.ker, IsLocalRing.maximalIdeal_eq_bot] using hker
    let sourceF : Spec (.of F) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L A)) ≫ source
    let ψ : ↑S →+* A := (algebraMap L A).comp φ
    have : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let target : Spec (.of A) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y
    have htargetClosed := base_comp_fromSpecStalk_closedPoint ψ
    have hcomm :
        Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ target = sourceF ≫ f := by
      have hψcat : CommRingCat.ofHom ψ = CommRingCat.ofHom φ ≫
          CommRingCat.ofHom (algebraMap L A) := by
        ext s
        rfl
      dsimp [target, sourceF]
      rw [hψcat, Spec.map_comp]
      simpa only [Category.assoc] using congrArg (fun g : Spec (.of L) ⟶ Y =>
        Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap L A)) ≫ g) hsourceTarget.symm
    have hη_eq_y : f η = y := by
      have h := congrArg (fun g : Spec (.of L) ⟶ Y => g (IsLocalRing.closedPoint L))
        hsourceTarget
      have hleft : (source ≫ f) (IsLocalRing.closedPoint L) = f η := by
        change f (source (IsLocalRing.closedPoint L)) = f η
        rw [show source (IsLocalRing.closedPoint L) = η from
          Scheme.fromSpecResidueField_apply η _]
      have hright : targetFromStalk (IsLocalRing.closedPoint L) = y := by
        exact base_comp_fromSpecStalk_closedPoint φ
      exact hleft.symm.trans (h.trans hright)
    exact ⟨{
      valuationRing := A
      fractionField := F
      genericPoint := η
      component := C
      component_mem := c.2
      isGenericPoint := hη
      toSource := sourceF
      toTarget := target
      maps_genericPoint := by
        change source.base (Spec.map (CommRingCat.ofHom (algebraMap L A))
          (Spec.map (CommRingCat.ofHom (algebraMap A F))
            (⟨⊥, inferInstance⟩ : PrimeSpectrum F))) = η
        have hp : Spec.map (CommRingCat.ofHom (algebraMap L A))
            (Spec.map (CommRingCat.ofHom (algebraMap A F))
              (⟨⊥, inferInstance⟩ : PrimeSpectrum F)) =
            (⟨⊥, inferInstance⟩ : PrimeSpectrum L) := Subsingleton.elim _ _
        rw [hp]
        exact Scheme.fromSpecResidueField_apply η _
      maps_closedPoint := htargetClosed
      commutes := hcomm
      residueFieldEquiv := fun hne => (hne hη_eq_y).elim
    }, hηx⟩
  · let : Algebra.EssFiniteType K L := RingHom.essFiniteType_algebraMap.mp hKL
    obtain ⟨A, hDVR, hFrac, hLocal⟩ :=
      exists_isDiscreteValuationRing_isFractionRing_of_not_isField K (L := L) hR
    let : CommRing A := inferInstance
    let : IsDomain A := inferInstance
    let : IsDiscreteValuationRing A := hDVR
    let : Algebra A L := inferInstance
    let : IsFractionRing A L := hFrac
    have : IsLocalHom (RingHom.rangeRestrict φ) :=
      IsLocalHom.of_surjective _ (RingHom.rangeRestrict_surjective φ)
    have : IsLocalHom (algebraMap R A) := hLocal
    let ψ : ↑S →+* A := (algebraMap R A).comp (RingHom.rangeRestrict φ)
    have hψL : (algebraMap A L).comp ψ = φ := by
      ext s
      change ((RingHom.rangeRestrict φ s : R) : L) = φ s
      rfl
    let : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let target : Spec (.of A) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y
    have htargetClosed := base_comp_fromSpecStalk_closedPoint ψ
    have hcomm :
        Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ target = source ≫ f := by
      have hcat : CommRingCat.ofHom ψ ≫
          CommRingCat.ofHom (algebraMap A L) = CommRingCat.ofHom φ := by
        ext s
        exact RingHom.congr_fun hψL s
      dsimp [target]
      rw [← Spec.map_comp_assoc, hcat]
      exact hsourceTarget.symm
    exact ⟨{
      valuationRing := A
      fractionField := L
      genericPoint := η
      component := C
      component_mem := c.2
      isGenericPoint := hη
      toSource := source
      toTarget := target
      maps_genericPoint := by
        change X.fromSpecResidueField η
          (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of L)) = η
        exact Scheme.fromSpecResidueField_apply η _
      maps_closedPoint := htargetClosed
      commutes := hcomm
      residueFieldEquiv := by
        intro hne
        refine ⟨RingEquiv.refl _, ?_⟩
        have hid : CommRingCat.ofHom (RingEquiv.refl (↑L)) =
            𝟙 (CommRingCat.of (↑L)) := by
          ext z
          rfl
        dsimp [source]
        rw [hid, Spec.map_id, Category.id_comp]
    }, hηx⟩

/-- A point in the closure of the image of a finite-type morphism into a locally Noetherian
scheme is reached by a discrete valuation ring, with generic point on a generic component of the
source. -/
@[stacks 0CM2]
theorem nonempty_discreteValuationSpecialization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y] (y : Y)
    (y_mem_closure : y ∈ closure (Set.range f.base)) :
    Nonempty (DiscreteValuationSpecialization f y) := by
  have hyker : y ∈ (f.ker.support : Set Y) := by rwa [f.support_ker]
  obtain ⟨x, hfx⟩ := exists_specializes_of_image_point f ⟨y, hyker⟩
  change f x ⤳ y at hfx
  obtain ⟨d, -⟩ := exists_discreteValuationSpecialization_genericPoint_specializes f hfx
  exact ⟨d⟩

end AlgebraicGeometry

end

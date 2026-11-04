module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion
public import StacksFrontier.RingTheory.Henselian.QuasiFiniteRingMaps
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# The generic-separable-degree weighting

A locally quasi-finite morphism locally of finite type onto a geometrically unibranch locally
Noetherian scheme carries a canonical weighting: the weight at a point of the source is the
generic separable degree of the induced map on strict henselizations, that is the number of
geometric points of the generic fibre of the strict henselization of the local ring at that
point over the strict henselization of the local ring at its image.

This file treats ind-étale local ring maps and strict henselizations: residue fields,
existence, uniqueness up to isomorphism and local maps between them. The weighting itself, listed
under the main results below, is constructed in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.Weighting`.

## Main results

* `AlgebraicGeometry.exists_weighting_genericSeparableDegree` produces the weighting and
  identifies each of its values with the generic separable degree.

## Implementation notes

The generic separable degree of a finite algebra over a field is expressed as the number of its
geometric points, that is of algebra homomorphisms from that algebra into an algebraic closure;
for a field factor this is its separable degree. The statement quantifies over all compatible
strict henselizations instead of choosing them, and the generic field of the strict henselization
of the target local ring is the residue field of its unique minimal prime.

## References

* [Stacks Project, Tag 0F3E](https://stacks.math.columbia.edu/tag/0F3E)
-/

public section

open AlgebraicGeometry
open IsLocalRing
open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private abbrev IsIndEtale {R S : Type u} [CommRing R] [CommRing S]
    (hom : R →+* S) : Prop :=
  let : Algebra R S := hom.toAlgebra
  StacksDraft.IndEtale R S

private theorem indEtale_respectsIso : RingHom.RespectsIso @IsIndEtale := by
  constructor
  · intro R S T _ _ _ hom equiv hind
    let : Algebra R S := hom.toAlgebra
    let : Algebra R T := (equiv.toRingHom.comp hom).toAlgebra
    exact StacksDraft.indEtale_of_equiv (RingEquiv.refl R) equiv (fun _ => rfl) hind
  · intro R S T _ _ _ hom equiv hind
    let : Algebra S T := hom.toAlgebra
    let : Algebra R T := (hom.comp equiv.toRingHom).toAlgebra
    exact StacksDraft.indEtale_of_equiv equiv.symm (RingEquiv.refl T)
      (fun element => congrArg hom (equiv.apply_symm_apply element).symm) hind

private theorem indEtale_localRingHom {R S : Type u} [CommRing R] [CommRing S]
    (hom : R →+* S) (het : hom.Etale) (prime : Ideal S) [prime.IsPrime] :
    let : Algebra (Localization.AtPrime (prime.comap hom)) (Localization.AtPrime prime) :=
      (Localization.localRingHom _ prime hom rfl).toAlgebra
    StacksDraft.IndEtale (Localization.AtPrime (prime.comap hom))
      (Localization.AtPrime prime) := by
  let : Algebra R S := hom.toAlgebra
  let : Algebra.Etale R S := het
  let : Algebra (Localization.AtPrime (prime.comap hom)) (Localization.AtPrime prime) :=
    (Localization.localRingHom _ prime hom rfl).toAlgebra
  let : IsScalarTower R (Localization.AtPrime (prime.comap hom))
      (Localization.AtPrime prime) :=
    .of_algebraMap_eq fun element =>
      (Localization.localRingHom_to_map _ prime hom rfl element).symm
  exact StacksDraft.indEtale_of_comp
    (StacksDraft.indEtale_atPrime (prime.comap hom))
    (StacksDraft.indEtale_comp
      (StacksDraft.indEtale_iff.mpr
        (CategoryTheory.ObjectProperty.le_ind (CommAlgCat.etale R) _ inferInstance))
      (StacksDraft.indEtale_atPrime prime))

private theorem indEtale_stalkMap {X Y : Scheme.{u}} (hom : X ⟶ Y)
    [Etale hom] (point : X) :
    let : Algebra (Y.presheaf.stalk (hom point)) (X.presheaf.stalk point) :=
      (hom.stalkMap point).hom.toAlgebra
    StacksDraft.IndEtale (Y.presheaf.stalk (hom point)) (X.presheaf.stalk point) := by
  exact HasRingHomProperty.stalkMap_of_respectsIso
    (P := @Etale) (Q' := @IsIndEtale)
    indEtale_respectsIso (fun hom het prime _ => indEtale_localRingHom hom het prime)
    inferInstance point

private theorem formallyUnramified_of_indEtale
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hind : StacksDraft.IndEtale R S) : Algebra.FormallyUnramified R S := by
  obtain ⟨index, _, _, presentation, hetale⟩ := StacksDraft.indEtale_iff.mp hind
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro target _ _ ideal hsquare hom₁ hom₂ heq
  suffices heq' : CommAlgCat.ofHom hom₁ = CommAlgCat.ofHom hom₂ from
    congrArg CommAlgCat.Hom.hom heq'
  apply presentation.isColimit.hom_ext
  intro element
  let : Algebra.Etale R (presentation.diag.obj element) := hetale element
  apply CommAlgCat.hom_ext
  apply Algebra.FormallyUnramified.lift_unique ideal ⟨2, by rw [hsquare]; rfl⟩
  exact congrArg (fun hom => hom.comp (presentation.ι.app element).hom) heq

private theorem weaklyEtale_of_indEtale
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hind : StacksDraft.IndEtale R S) : Algebra.WeaklyEtale R S := by
  obtain ⟨index, _, _, presentation, hetale⟩ := StacksDraft.indEtale_iff.mp hind
  exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} R).2.2
    index presentation.diag presentation.cocone presentation.isColimit
    (fun element => by
      let : Algebra.Etale R (presentation.diag.obj element) := hetale element
      infer_instance)

private theorem isSeparable_residueField_of_indEtale
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hind : StacksDraft.IndEtale R S) :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
  let equivR := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let equivS := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField S) (maximalIdeal S).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal S))
  let hom := Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S)
    (algebraMap R S) (maximalIdeal_comap (algebraMap R S)).symm
  let : Algebra (maximalIdeal R).ResidueField (maximalIdeal S).ResidueField :=
    hom.toAlgebra
  have hsep : Algebra.IsSeparable (maximalIdeal R).ResidueField
      (maximalIdeal S).ResidueField :=
    (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale R S
      (weaklyEtale_of_indEtale hind) (maximalIdeal R) (maximalIdeal S)
      (maximalIdeal_comap (algebraMap R S)).symm).1
  let : Algebra (ResidueField R) (maximalIdeal S).ResidueField :=
    (hom.comp equivR.toRingHom).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField
      (maximalIdeal S).ResidueField := .of_algebraMap_eq' rfl
  have hequivS : equivS.toRingHom.comp (algebraMap (ResidueField R) (ResidueField S)) =
      hom.comp equivR.toRingHom := by
    ext element
    obtain ⟨element, rfl⟩ := residue_surjective element
    show algebraMap S (maximalIdeal S).ResidueField (algebraMap R S element) =
      hom (algebraMap R (maximalIdeal R).ResidueField element)
    exact (Ideal.ResidueField.map_algebraMap _ _ _ _ _).symm
  let : IsScalarTower (ResidueField R) (ResidueField S)
      (maximalIdeal S).ResidueField := .of_algebraMap_eq' hequivS.symm
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable equivR
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal S).ResidueField :=
    Algebra.IsSeparable.trans _ (maximalIdeal R).ResidueField _
  exact Algebra.IsSeparable.of_algHom (ResidueField R) (maximalIdeal S).ResidueField
    (IsScalarTower.toAlgHom (ResidueField R)
      (ResidueField S) (maximalIdeal S).ResidueField)

private theorem isSepClosure_residueField_of_indEtale
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsSepClosed (ResidueField S)]
    (hind : StacksDraft.IndEtale R S) :
    IsSepClosure (ResidueField R) (ResidueField S) :=
  ⟨inferInstance, isSeparable_residueField_of_indEtale hind⟩

/-- A composite of local `R`-algebra maps `B → A → B` fixing the residue classes is the
identity. -/
private theorem comp_eq_id_of_residue_eq
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HenselianLocalRing B] [IsLocalRing A] [Algebra R A] [Algebra R B]
    (hB : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R (ULift.{u} B)))
    (f : B →ₐ[R] A) (g : A →ₐ[R] B) [IsLocalHom f] [IsLocalHom g]
    (hfg : ∀ element, residue B (g (f element)) = residue B element) :
    g.comp f = AlgHom.id R B := by
  obtain ⟨_, _, hunique⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale hB (RingHom.id _) rfl
  have hcomp : IsLocalHom (g.comp f) :=
    ⟨fun element hunit => IsLocalHom.map_nonunit (f := f) element
      (IsLocalHom.map_nonunit (f := g) (f element) hunit)⟩
  have hid : IsLocalHom (AlgHom.id R B) := ⟨fun _ hunit => hunit⟩
  refine (hunique _ ⟨hcomp, ?_⟩).trans (hunique _ ⟨hid, rfl⟩).symm
  ext element
  exact hfg element

private theorem exists_algEquiv_of_indEtale_of_residueFieldEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B] [Algebra R A] [Algebra R B]
    (hA : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R (ULift.{u} A)))
    (hB : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R (ULift.{u} B)))
    (equiv : ResidueField A ≃+* ResidueField B)
    (hcompat : equiv.toRingHom.comp ((residue A).comp (algebraMap R A)) =
      (residue B).comp (algebraMap R B)) :
    ∃ algebraEquiv : A ≃ₐ[R] B,
      (residue B).comp algebraEquiv.toRingHom = equiv.toRingHom.comp (residue A) := by
  have hcompatSymm : equiv.symm.toRingHom.comp
      ((residue B).comp (algebraMap R B)) =
      (residue A).comp (algebraMap R A) := by
    ext element
    have heq := RingHom.congr_fun hcompat element
    change equiv (residue A (algebraMap R A element)) =
      residue B (algebraMap R B element) at heq
    show equiv.symm (residue B (algebraMap R B element)) = _
    rw [← heq]
    exact equiv.symm_apply_apply _
  obtain ⟨forward, ⟨hforwardLocal, hforward⟩, _⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hA equiv.toRingHom hcompat
  obtain ⟨backward, ⟨hbackwardLocal, hbackward⟩, _⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hB equiv.symm.toRingHom hcompatSymm
  let : IsLocalHom forward := hforwardLocal
  let : IsLocalHom backward := hbackwardLocal
  have hforwardApply (element : A) :
      residue B (forward element) = equiv (residue A element) :=
    RingHom.congr_fun hforward element
  have hbackwardApply (element : B) :
      residue A (backward element) = equiv.symm (residue B element) :=
    RingHom.congr_fun hbackward element
  exact ⟨AlgEquiv.ofAlgHom forward backward
    (comp_eq_id_of_residue_eq hB backward forward fun element => by
      rw [hforwardApply, hbackwardApply, equiv.apply_symm_apply])
    (comp_eq_id_of_residue_eq hA forward backward fun element => by
      rw [hbackwardApply, hforwardApply, equiv.symm_apply_apply]), hforward⟩

private theorem algHom_bijective_of_isSepClosure
    {F A B : Type*} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B] [IsSepClosure F A] [IsSepClosure F B]
    (hom : A →ₐ[F] B) : Function.Bijective hom := by
  let : Algebra A B := hom.toRingHom.toAlgebra
  let : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun element =>
    (hom.commutes element).symm
  let : IsSepClosed A := IsSepClosure.sep_closed F
  let : Algebra.IsSeparable A B := Algebra.isSeparable_tower_top_of_isSeparable F A B
  exact IsSepClosed.algebraMap_bijective A B

private theorem exists_algHom_factor_of_isPurelyInseparable
    {F A B L : Type*} [Field F] [Field A] [Field B] [Field L]
    [Algebra F A] [Algebra F B] [Algebra F L] [Algebra B L]
    [IsScalarTower F B L] [Algebra.IsSeparable F A] [IsPurelyInseparable B L]
    (hom : A →ₐ[F] L) :
    ∃ factor : A →ₐ[F] B,
      (IsScalarTower.toAlgHom F B L).comp factor = hom := by
  let inclusion := IsScalarTower.toAlgHom F B L
  let equiv := AlgEquiv.ofInjective inclusion inclusion.injective
  have hrange (element : A) : hom element ∈ inclusion.range :=
    IsPurelyInseparable.inseparable B (hom element)
      (IsSeparable.tower_top B ((Algebra.IsSeparable.isSeparable F element).map
        hom hom.injective))
  refine ⟨equiv.symm.toAlgHom.comp (hom.codRestrict inclusion.range hrange), ?_⟩
  ext element
  exact congrArg Subtype.val (equiv.apply_symm_apply
    (hom.codRestrict inclusion.range hrange element))

private theorem exists_algEquiv_eq_of_localAlgHom_of_indEtale
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B] [Algebra R A] [Algebra R B]
    (hA : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R (ULift.{u} A)))
    (hB : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R (ULift.{u} B)))
    (hom : A →ₐ[R] B) [IsLocalHom hom.toRingHom]
    (hresidue : Function.Bijective (ResidueField.map hom.toRingHom)) :
    ∃ equiv : A ≃ₐ[R] B, equiv.toAlgHom = hom := by
  let residueEquiv := RingEquiv.ofBijective (ResidueField.map hom.toRingHom) hresidue
  have hcompat : residueEquiv.toRingHom.comp
      ((residue A).comp (algebraMap R A)) =
      (residue B).comp (algebraMap R B) := by
    ext element
    show ResidueField.map hom.toRingHom (residue A (algebraMap R A element)) = _
    rw [ResidueField.map_residue]
    show residue B (hom (algebraMap R A element)) = residue B (algebraMap R B element)
    rw [hom.commutes]
  obtain ⟨equiv, hequiv⟩ :=
    exists_algEquiv_of_indEtale_of_residueFieldEquiv hA hB residueEquiv hcompat
  let : IsLocalHom hom := ⟨fun element hunit =>
    (inferInstance : IsLocalHom hom.toRingHom).map_nonunit element hunit⟩
  obtain ⟨_, _, hunique⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hA residueEquiv.toRingHom hcompat
  refine ⟨equiv, (hunique equiv.toAlgHom ⟨inferInstance, hequiv⟩).trans
    (hunique hom ⟨inferInstance, ?_⟩).symm⟩
  ext element
  exact ResidueField.map_residue hom.toRingHom element

private theorem exists_residueFieldEquiv_of_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization R κ Rsh) :
    ∃ equiv : κ ≃+* ResidueField Rsh, ∀ element : R,
      equiv (algebraMap (maximalIdeal R).ResidueField κ
        (algebraMap R (maximalIdeal R).ResidueField element)) =
      residue Rsh (algebraMap R Rsh element) := by
  let := hsh.isLocalHom
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField Rsh) (maximalIdeal Rsh).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal Rsh))
  refine ⟨hsh.residueFieldEquiv.trans quotientEquiv.symm.toRingEquiv, ?_⟩
  intro element
  apply quotientEquiv.injective
  show quotientEquiv (quotientEquiv.symm
    (hsh.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κ
      (algebraMap R (maximalIdeal R).ResidueField element)))) = _
  rw [quotientEquiv.apply_symm_apply]
  exact (RingHom.congr_fun hsh.residueFieldEquiv_comp
    (algebraMap R (maximalIdeal R).ResidueField element)).trans
      (Ideal.ResidueField.map_algebraMap _ _ _ _ _)

theorem isSepClosure_residueField_of_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    [IsLocalHom (algebraMap R Rsh)]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization R κ Rsh) :
    IsSepClosure (ResidueField R) (ResidueField Rsh) := by
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable quotientEquiv
  let : Algebra (ResidueField R) κ :=
    ((algebraMap (maximalIdeal R).ResidueField κ).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsSeparable (ResidueField R) κ :=
    Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κ
  obtain ⟨residueEquiv, hresidue⟩ := exists_residueFieldEquiv_of_strictHenselization R κ Rsh hsh
  let equiv : κ ≃ₐ[ResidueField R] ResidueField Rsh :=
    { residueEquiv with
      commutes' := fun element => by
        obtain ⟨element, rfl⟩ := residue_surjective element
        exact hresidue element }
  let : IsSepClosed κ := IsSepClosure.sep_closed (maximalIdeal R).ResidueField
  let : IsSepClosed (ResidueField Rsh) := IsSepClosed.of_ringEquiv residueEquiv.symm
  exact ⟨inferInstance, AlgEquiv.Algebra.isSeparable equiv⟩

private theorem isHenselization_residueField_of_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    [IsLocalHom (algebraMap R Rsh)]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization R κ Rsh) :
    IsHenselization R (ResidueField Rsh) Rsh :=
  ⟨hsh.henselian, hsh.isFilteredColimitEtale, RingEquiv.refl _, fun _ => rfl⟩

private theorem isSepClosure_idealResidueField_of_isSepClosure
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [IsSepClosure (ResidueField R) (ResidueField T)] :
    ∃ algebra : Algebra (maximalIdeal R).ResidueField (maximalIdeal T).ResidueField,
      @IsSepClosure (maximalIdeal R).ResidueField _ (maximalIdeal T).ResidueField _ algebra ∧
      ∀ element : R,
        @algebraMap (maximalIdeal R).ResidueField (maximalIdeal T).ResidueField _ _ algebra
          (algebraMap R (maximalIdeal R).ResidueField element) =
          algebraMap T (maximalIdeal T).ResidueField (algebraMap R T element) := by
  let equivR := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let equivT := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField T) (maximalIdeal T).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal T))
  let : Algebra (maximalIdeal R).ResidueField (ResidueField R) :=
    equivR.symm.toRingHom.toAlgebra
  let : Algebra (maximalIdeal R).ResidueField (ResidueField T) :=
    ((algebraMap (ResidueField R) (ResidueField T)).comp equivR.symm.toRingHom).toAlgebra
  let : IsScalarTower (maximalIdeal R).ResidueField (ResidueField R) (ResidueField T) :=
    .of_algebraMap_eq' rfl
  let : Algebra.IsSeparable (maximalIdeal R).ResidueField (ResidueField R) :=
    AlgEquiv.Algebra.isSeparable
      (AlgEquiv.ofBijective (Algebra.ofId _ _) equivR.symm.bijective)
  let : Algebra.IsSeparable (maximalIdeal R).ResidueField (ResidueField T) :=
    Algebra.IsSeparable.trans _ (ResidueField R) _
  let : Algebra (maximalIdeal R).ResidueField (maximalIdeal T).ResidueField :=
    (equivT.toRingHom.comp (algebraMap (maximalIdeal R).ResidueField (ResidueField T))).toAlgebra
  let : IsScalarTower (maximalIdeal R).ResidueField (ResidueField T)
      (maximalIdeal T).ResidueField := .of_algebraMap_eq' rfl
  let : IsSepClosed (ResidueField T) := IsSepClosure.sep_closed (ResidueField R)
  refine ⟨inferInstance, ⟨IsSepClosed.of_ringEquiv equivT.symm.toRingEquiv,
    AlgEquiv.Algebra.isSeparable (equivT.restrictScalars (maximalIdeal R).ResidueField)⟩, ?_⟩
  intro element
  show equivT (algebraMap (ResidueField R) (ResidueField T)
    (equivR.symm (algebraMap R (maximalIdeal R).ResidueField element))) = _
  have hR : algebraMap R (maximalIdeal R).ResidueField element = equivR (residue R element) :=
    (IsScalarTower.algebraMap_apply R (ResidueField R) _ element).symm
  rw [hR, equivR.symm_apply_apply, ResidueField.algebraMap_residue]
  exact IsScalarTower.algebraMap_apply T (ResidueField T) _ _

private theorem exists_isStrictHenselization_of_indEtale
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R]
    [Algebra R T] [IsLocalHom (algebraMap R T)] [HenselianLocalRing T]
    [IsSepClosure (ResidueField R) (ResidueField T)]
    (hind : StacksDraft.IndEtale R T) :
    ∃ algebra : Algebra (maximalIdeal R).ResidueField (maximalIdeal T).ResidueField,
      ∃ hsep : @IsSepClosure (maximalIdeal R).ResidueField _
        (maximalIdeal T).ResidueField _ algebra,
      Nonempty (@Stacks.StrictHenselization.IsStrictHenselization R _ _
        (maximalIdeal T).ResidueField _ algebra hsep T _ _ _) := by
  obtain ⟨algebra, hsep, hcompat⟩ := isSepClosure_idealResidueField_of_isSepClosure (R := R)
    (T := T)
  let := algebra
  let := hsep
  refine ⟨algebra, hsep, ⟨{
    isLocalHom := inferInstance
    henselian := inferInstance
    sepClosed := IsSepClosure.sep_closed (maximalIdeal R).ResidueField
    isFilteredColimitEtale := hind
    maximalIdeal_map := ?_
    residueFieldEquiv := RingEquiv.refl _
    residueFieldEquiv_comp := ?_ }⟩⟩
  · exact CommAlgCat.map_maximalIdeal_of_ind_etale (StacksDraft.indEtale_iff.mp hind)
  · refine RingHom.ext fun element => ?_
    obtain ⟨element, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) element
    exact (hcompat element).trans (Ideal.ResidueField.map_algebraMap _ _ _ _ _).symm

/-- The composite of local ring maps in a tower is local. -/
private theorem isLocalHom_algebraMap_of_tower {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] :
    IsLocalHom (algebraMap R T) := by
  rw [IsScalarTower.algebraMap_eq R S T]
  exact RingHom.isLocalHom_comp _ _

/-- Over a separable residue field extension, a separable closure of the residue field of the
middle ring is one for the residue field of the base. -/
private theorem isSepClosure_residueField_of_tower {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] [IsLocalHom (algebraMap R S)]
    [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap R T)]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [IsSepClosure (ResidueField S) (ResidueField T)] :
    IsSepClosure (ResidueField R) (ResidueField T) :=
  ⟨IsSepClosure.sep_closed (ResidueField S),
    Algebra.IsSeparable.trans (ResidueField R) (ResidueField S) (ResidueField T)⟩

private theorem exists_isStrictHenselization_of_indEtale_comp
    {R S Ssh : Type u} [CommRing R] [CommRing S] [CommRing Ssh]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing Ssh]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Algebra S Ssh] [Algebra R Ssh] [IsScalarTower R S Ssh]
    (κS : Type u) [Field κS] [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (hind : StacksDraft.IndEtale R S)
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh) :
    ∃ algebra : Algebra (maximalIdeal R).ResidueField (maximalIdeal Ssh).ResidueField,
      ∃ hsep : @IsSepClosure (maximalIdeal R).ResidueField _
        (maximalIdeal Ssh).ResidueField _ algebra,
      Nonempty (@Stacks.StrictHenselization.IsStrictHenselization R _ _
        (maximalIdeal Ssh).ResidueField _ algebra hsep Ssh _ _ _) := by
  let := hSsh.henselian
  let := hSsh.isLocalHom
  let : IsLocalHom (algebraMap R Ssh) := isLocalHom_algebraMap_of_tower (S := S)
  let := isSepClosure_residueField_of_strictHenselization S κS Ssh hSsh
  let : IsSepClosure (ResidueField R) (ResidueField Ssh) :=
    isSepClosure_residueField_of_tower (S := S)
  exact exists_isStrictHenselization_of_indEtale
    (StacksDraft.indEtale_comp hind hSsh.isFilteredColimitEtale)

private theorem exists_algEquiv_of_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κA κB : Type u) [Field κA] [Field κB]
    [Algebra (maximalIdeal R).ResidueField κA]
    [Algebra (maximalIdeal R).ResidueField κB]
    [IsSepClosure (maximalIdeal R).ResidueField κA]
    [IsSepClosure (maximalIdeal R).ResidueField κB]
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra R B]
    (hA : Stacks.StrictHenselization.IsStrictHenselization R κA A)
    (hB : Stacks.StrictHenselization.IsStrictHenselization R κB B) : Nonempty (A ≃ₐ[R] B) := by
  let := hA.henselian
  let := hB.henselian
  obtain ⟨residueEquivA, hresidueA⟩ :=
    exists_residueFieldEquiv_of_strictHenselization R κA A hA
  obtain ⟨residueEquivB, hresidueB⟩ :=
    exists_residueFieldEquiv_of_strictHenselization R κB B hB
  let closureEquiv := IsSepClosure.equiv (maximalIdeal R).ResidueField κA κB
  let residueEquiv := residueEquivA.symm.trans
    (closureEquiv.toRingEquiv.trans residueEquivB)
  have hcompat : residueEquiv.toRingHom.comp
      ((residue A).comp (algebraMap R A)) =
      (residue B).comp (algebraMap R B) := by
    ext element
    show residueEquivB (closureEquiv
      (residueEquivA.symm (residue A (algebraMap R A element)))) = _
    rw [← hresidueA, residueEquivA.symm_apply_apply, closureEquiv.commutes, hresidueB]
    rfl
  obtain ⟨algebraEquiv, _⟩ := exists_algEquiv_of_indEtale_of_residueFieldEquiv
    hA.isFilteredColimitEtale hB.isFilteredColimitEtale residueEquiv hcompat
  exact ⟨algebraEquiv⟩

private theorem exists_algEquiv_of_indEtale_strictHenselizations
    {R S Rsh Ssh : Type u}
    [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing Rsh] [IsLocalRing Ssh]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Algebra R Rsh] [Algebra S Ssh] [Algebra R Ssh] [Algebra Rsh Ssh]
    [IsScalarTower R S Ssh] [IsScalarTower R Rsh Ssh]
    [IsLocalHom (algebraMap Rsh Ssh)]
    (κR κS : Type u) [Field κR] [Field κS]
    [Algebra (maximalIdeal R).ResidueField κR]
    [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (hRS : StacksDraft.IndEtale R S)
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh) :
    ∃ equiv : Rsh ≃ₐ[R] Ssh,
      equiv.toAlgHom = IsScalarTower.toAlgHom R Rsh Ssh := by
  let := hRsh.isLocalHom
  let := hSsh.isLocalHom
  let := hRsh.henselian
  let := hSsh.henselian
  let : IsLocalHom (algebraMap R Ssh) := isLocalHom_algebraMap_of_tower (S := S)
  let := isSepClosure_residueField_of_strictHenselization R κR Rsh hRsh
  let := isSepClosure_residueField_of_strictHenselization S κS Ssh hSsh
  let : IsSepClosure (ResidueField R) (ResidueField Ssh) :=
    isSepClosure_residueField_of_tower (S := S)
  have hresidue : Function.Bijective (ResidueField.map (algebraMap Rsh Ssh)) :=
    algHom_bijective_of_isSepClosure
      (IsScalarTower.toAlgHom (ResidueField R) (ResidueField Rsh) (ResidueField Ssh))
  let : IsLocalHom (IsScalarTower.toAlgHom R Rsh Ssh).toRingHom :=
    inferInstanceAs (IsLocalHom (algebraMap Rsh Ssh))
  exact exists_algEquiv_eq_of_localAlgHom_of_indEtale hRsh.isFilteredColimitEtale
    (StacksDraft.indEtale_comp hRS hSsh.isFilteredColimitEtale)
    (IsScalarTower.toAlgHom R Rsh Ssh) hresidue

private theorem exists_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh),
      Nonempty (Stacks.StrictHenselization.IsStrictHenselization R κ Rsh) := by
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable quotientEquiv
  let : Algebra (ResidueField R) κ :=
    ((algebraMap (maximalIdeal R).ResidueField κ).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsSepClosure (ResidueField R) κ :=
    ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
      Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κ⟩
  obtain ⟨Rh, ringRh, algebraRh, localRh, localMapRh, _, indRh, _, residueRh⟩ :=
    IsLocalRing.exists_henselization R
  let := ringRh
  let := algebraRh
  let := localRh
  let := localMapRh
  obtain ⟨Rsh, ringRsh, localRsh, algebraRsh, algebraRhRsh, towerRsh,
    localMapRhRsh, henselianRsh, sepClosedRsh, indRsh, maximalRsh,
    residueEquiv, hresidueEquiv⟩ :=
    IsLocalRing.exists_strictHenselization R Rh indRh residueRh.2 κ
  let := ringRsh
  let := localRsh
  let := algebraRsh
  let := algebraRhRsh
  let := towerRsh
  let := localMapRhRsh
  let : IsLocalHom (algebraMap R Rsh) := isLocalHom_algebraMap_of_tower (S := Rh)
  let quotientEquivSh := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField Rsh) (maximalIdeal Rsh).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal Rsh))
  let := sepClosedRsh
  let residueEquivSh := residueEquiv.trans quotientEquivSh.toRingEquiv
  refine ⟨Rsh, ringRsh, localRsh, algebraRsh, ⟨{
    isLocalHom := inferInstance
    henselian := henselianRsh
    sepClosed := IsSepClosed.of_ringEquiv quotientEquivSh.symm.toRingEquiv
    isFilteredColimitEtale := StacksDraft.indEtale_iff.mpr indRsh
    maximalIdeal_map := maximalRsh
    residueFieldEquiv := residueEquivSh
    residueFieldEquiv_comp := ?_ }⟩⟩
  ext element
  show quotientEquivSh (residueEquiv
    (algebraMap (ResidueField R) κ (residue R element))) = _
  rw [hresidueEquiv]
  exact (Ideal.ResidueField.map_algebraMap _ _ _ _ element).symm

private theorem exists_localAlgHom_of_strictHenselization
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (κR κS : Type u) [Field κR] [Field κS]
    [Algebra (maximalIdeal R).ResidueField κR]
    [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (Rsh Ssh : Type u) [CommRing Rsh] [CommRing Ssh] [IsLocalRing Rsh]
    [IsLocalRing Ssh] [Algebra R Rsh] [Algebra S Ssh]
    [Algebra R Ssh] [IsScalarTower R S Ssh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh) :
    ∃ hom : Rsh →ₐ[R] Ssh, IsLocalHom hom := by
  let := hRsh.henselian
  let := hSsh.henselian
  obtain ⟨equivR, hresidueR⟩ :=
    exists_residueFieldEquiv_of_strictHenselization R κR Rsh hRsh
  obtain ⟨equivS, hresidueS⟩ :=
    exists_residueFieldEquiv_of_strictHenselization S κS Ssh hSsh
  let residueMap : (maximalIdeal R).ResidueField →+* (maximalIdeal S).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
      (maximalIdeal_comap (algebraMap R S)).symm
  let : Algebra (maximalIdeal R).ResidueField κS :=
    ((algebraMap (maximalIdeal S).ResidueField κS).comp residueMap).toAlgebra
  let : IsSepClosed κS := IsSepClosure.sep_closed (maximalIdeal S).ResidueField
  let closureMap : κR →ₐ[(maximalIdeal R).ResidueField] κS := IsSepClosed.lift
  let fieldMap : ResidueField Rsh →+* ResidueField Ssh :=
    equivS.toRingHom.comp (closureMap.toRingHom.comp equivR.symm.toRingHom)
  have hcompat : fieldMap.comp ((residue Rsh).comp (algebraMap R Rsh)) =
      (residue Ssh).comp (algebraMap R Ssh) := by
    ext element
    show equivS (closureMap (equivR.symm
      (residue Rsh (algebraMap R Rsh element)))) = _
    rw [← hresidueR, equivR.symm_apply_apply, closureMap.commutes]
    show equivS (algebraMap (maximalIdeal S).ResidueField κS
      (residueMap (algebraMap R (maximalIdeal R).ResidueField element))) = _
    rw [Ideal.ResidueField.map_algebraMap, hresidueS,
      ← IsScalarTower.algebraMap_apply R S Ssh]
    rfl
  obtain ⟨hom, hlocal, _⟩ :=
    (StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hRsh.isFilteredColimitEtale fieldMap hcompat).exists
  exact ⟨hom, hlocal⟩

end AlgebraicGeometry

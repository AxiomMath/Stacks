module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# Specializations realized by discrete valuation rings

For a specialization of points on a locally Noetherian scheme, there is a morphism from the
spectrum of a discrete valuation ring whose generic and closed points map to the given points.
For a strict specialization, the residue field at the generic point can moreover be prescribed
up to an isomorphism of field extensions.

## Main results

* `AlgebraicGeometry.exists_dvr_morphism_of_specializes` realizes a specialization by a morphism
  from the spectrum of a discrete valuation ring.
* `AlgebraicGeometry.exists_dvr_morphism_of_specializes_with_residueField_equiv` realizes a
  strict specialization with a prescribed finitely generated extension of the residue field at
  the generic point.

## Implementation notes

The first result states part (1) and the second states part (2), including again the pointwise
properties of the morphism. Mathlib's `genericPoint` and `IsLocalRing.closedPoint` represent the
generic and special points of the spectrum. A finitely generated extension of fields is
expressed by `Algebra.EssFiniteType`. The displayed compatibility of the ring equivalence with
`Scheme.Hom.residueFieldMap` says precisely that it is an isomorphism of extensions of the
residue field at the specializing point.

## References

* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

private lemma residueFieldMap_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (z : X) : Function.Surjective (f.residueFieldMap z).hom := by
  intro a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, hc⟩ := f.stalkMap_surjective z b
  refine ⟨IsLocalRing.residue (Y.presheaf.stalk (f z)) c, ?_⟩
  show (IsLocalRing.ResidueField.map (f.stalkMap z).hom) _ = _
  rw [IsLocalRing.ResidueField.map_residue]
  simpa using congrArg (fun t => IsLocalRing.residue (X.presheaf.stalk z) t) hc

private noncomputable def specResidueFieldEquiv {R : CommRingCat.{u}}
    (y : Spec R) [hy : y.asIdeal.IsPrime] :
    (Spec R).residueField y ≃+* y.asIdeal.ResidueField :=
  RingEquiv.ofBijective (Scheme.Spec.residueFieldIso R y).hom.hom
    (ConcreteCategory.bijective_of_isIso _)

private noncomputable def fromSpecStalk_residueEquiv {X : Scheme.{u}} (x x' : X)
    (y : Spec (X.presheaf.stalk x)) [hy' : y.asIdeal.IsPrime]
    (hy : X.fromSpecStalk x y = x') :
    X.residueField x' ≃+* y.asIdeal.ResidueField := by
  let c : X.residueField x' ≃+* X.residueField (X.fromSpecStalk x y) :=
    RingEquiv.ofBijective ((X.residueFieldCongr hy.symm).hom).hom
      (ConcreteCategory.bijective_of_isIso _)
  let i : X.residueField (X.fromSpecStalk x y) ≃+*
      (Spec (X.presheaf.stalk x)).residueField y :=
    RingEquiv.ofBijective ((X.fromSpecStalk x).residueFieldMap y).hom
      ⟨RingHom.injective _, residueFieldMap_surjective (X.fromSpecStalk x) y⟩
  exact c.trans (i.trans (specResidueFieldEquiv y))

private lemma specStalkResidueFieldMap_bridge {X : Scheme.{u}} {S T : CommRingCat.{u}}
    (i : Spec S ⟶ X) (y : Spec S) [hy' : y.asIdeal.IsPrime]
    {x : X} (hy : i y = x)
    (g : S ⟶ T) (η : Spec T) [hη' : η.asIdeal.IsPrime]
    (hη : Spec.map g η = y) :
    ((X.residueFieldCongr hy).inv ≫ i.residueFieldMap y ≫
      (Scheme.Spec.residueFieldIso S y).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map y.asIdeal η.asIdeal g.hom
        (by rw [← hη]; rfl))).hom =
    ((X.residueFieldCongr (by simpa [hη] using hy)).inv ≫
      (Spec.map g ≫ i).residueFieldMap η ≫
      (Scheme.Spec.residueFieldIso T η).hom).hom := by
  subst y
  rw [← specResidueFieldMap_bridge g η]
  simp only [CommRingCat.ofHom_hom, Scheme.residueFieldMap_comp,
    Iso.hom_inv_id_assoc]
  rfl

/-- A point of the spectrum of a stalk that does not map to the point itself has a quotient that
is not a field. -/
private lemma not_isField_quotient_of_fromSpecStalk_ne {X : Scheme.{u}} {x : X}
    (y : Spec (X.presheaf.stalk x)) (hy : X.fromSpecStalk x y ≠ x) :
    ¬ IsField (X.presheaf.stalk x ⧸ y.asIdeal) := by
  intro hfield
  refine hy ?_
  rw [show y = IsLocalRing.closedPoint _ from PrimeSpectrum.ext
    (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hfield)),
    Scheme.fromSpecStalk_closedPoint]

private noncomputable def residueFieldEquivOfEqBot {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) [I.IsPrime]
    (hI : I = ⊥) : I.ResidueField ≃+* K :=
  (Ideal.residueFieldRingEquiv I ⊥ (RingEquiv.refl A) (hI.trans (by ext; rfl))).trans
    (IsLocalization.algEquiv (nonZeroDivisors A) _ K).toRingEquiv

private lemma residueFieldEquivOfEqBot_algebraMap {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) [I.IsPrime]
    (hI : I = ⊥) (b : A) :
    residueFieldEquivOfEqBot K I hI (algebraMap A I.ResidueField b) = algebraMap A K b := by
  have h₀ : I = Ideal.comap (RingEquiv.refl A : A →+* A) ⊥ := hI.trans (by ext; rfl)
  rw [residueFieldEquivOfEqBot, RingEquiv.trans_apply]
  show (IsLocalization.algEquiv (nonZeroDivisors A) (⊥ : Ideal A).ResidueField K).toRingEquiv
    (Ideal.ResidueField.map I ⊥ (RingEquiv.refl A) h₀ (algebraMap A I.ResidueField b)) = _
  rw [Ideal.ResidueField.map_algebraMap]
  exact (IsLocalization.algEquiv (nonZeroDivisors A) _ K).commutes' b

/-- A prime `p` of a Noetherian local ring with `S ⧸ p` not a field is the preimage of `⊥` under a
local homomorphism to a discrete valuation ring whose fraction field is a prescribed finitely
generated extension of the residue field at `p`. -/
private theorem exists_isDiscreteValuationRing_comap_bot_eq {S : Type u} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] (p : Ideal S) [p.IsPrime] (hp : ¬ IsField (S ⧸ p))
    {F : Type u} [Field F] (e₀ : F ≃+* p.ResidueField) (K : Type u) [Field K] [Algebra F K]
    [Algebra.EssFiniteType F K] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : Algebra A K) (_ : IsFractionRing A K) (j : S →+* A) (_ : IsLocalHom j),
      Ideal.comap j ⊥ = p ∧
        ∀ s, algebraMap A K (j s) = algebraMap F K (e₀.symm (algebraMap S p.ResidueField s)) := by
  have : IsLocalRing (S ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : Algebra (S ⧸ p) F :=
    (e₀.symm.toRingHom.comp (algebraMap (S ⧸ p) p.ResidueField)).toAlgebra
  have : IsFractionRing (S ⧸ p) F :=
    IsFractionRing.of_algEquiv (AlgEquiv.ofRingEquiv (f := e₀.symm) fun _ => rfl)
  let : Algebra (S ⧸ p) K := ((algebraMap F K).comp (algebraMap (S ⧸ p) F)).toAlgebra
  have : IsScalarTower (S ⧸ p) F K := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨A, hDVR, hfrac, hlocal⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField F (L := K) hp
  have : IsScalarTower (S ⧸ p) A K := IsScalarTower.of_algebraMap_eq' rfl
  have hinjK : Function.Injective (algebraMap (S ⧸ p) K) :=
    (algebraMap F K).injective.comp (IsFractionRing.injective (S ⧸ p) F)
  have hinj : Function.Injective (algebraMap (S ⧸ p) A) := fun a b hab => hinjK (by
    rw [IsScalarTower.algebraMap_apply (S ⧸ p) A K a, IsScalarTower.algebraMap_apply (S ⧸ p) A K b,
      hab])
  refine ⟨A, inferInstance, inferInstance, hDVR, inferInstance, hfrac,
    (algebraMap (S ⧸ p) A).comp (Ideal.Quotient.mk p), RingHom.isLocalHom_comp _ _, ?_,
    fun s => ?_⟩
  · ext s
    simp [map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · show algebraMap F K (e₀.symm (algebraMap (S ⧸ p) p.ResidueField (Ideal.Quotient.mk p s))) = _
    rw [Ideal.algebraMap_quotient_residueField_mk]

/-- The closed point of the spectrum of a local ring `A` with a local map from the stalk at `x`
maps to `x`. -/
private lemma spec_map_fromSpecStalk_closedPoint {X : Scheme.{u}} (x : X) {A : Type u}
    [CommRing A] [IsLocalRing A] (j : X.presheaf.stalk x →+* A) [IsLocalHom j] :
    (Spec.map (CommRingCat.ofHom j) ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint A) = x := by
  show X.fromSpecStalk x (PrimeSpectrum.comap j (IsLocalRing.closedPoint A)) = x
  rw [IsLocalRing.comap_closedPoint j, Scheme.fromSpecStalk_closedPoint]

private lemma exists_dvr_morphism_of_comap_bot_eq {X : Scheme.{u}} {x x' : X}
    (y : Spec (X.presheaf.stalk x)) (hy : X.fromSpecStalk x y = x')
    (K : Type u) [Field K] [Algebra (X.residueField x') K]
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]
    (j : X.presheaf.stalk x →+* A) [IsLocalHom j] (hj : Ideal.comap j ⊥ = y.asIdeal)
    (hjK : ∀ s, algebraMap A K (j s) = algebraMap (X.residueField x') K
      ((fromSpecStalk_residueEquiv x x' y hy).symm (algebraMap _ y.asIdeal.ResidueField s))) :
    ∃ (f : Spec (.of A) ⟶ X) (hη : f (genericPoint (Spec (.of A))) = x'),
      f (IsLocalRing.closedPoint A) = x ∧
        ∃ e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≃+* K,
          ∀ a : X.residueField x',
            e (f.residueFieldMap (genericPoint (Spec (.of A)))
              ((X.residueFieldCongr hη.symm).hom a)) =
              algebraMap (X.residueField x') K a := by
  let η := genericPoint (Spec (.of A))
  have : η.asIdeal.IsPrime := η.isPrime
  have hηideal : η.asIdeal = ⊥ := by
    show (genericPoint (Spec (.of A)) : PrimeSpectrum A).asIdeal = ⊥
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.asIdeal_bot
  have hgen : Spec.map (CommRingCat.ofHom j) η = y :=
    PrimeSpectrum.ext ((congrArg (Ideal.comap j) hηideal).trans hj)
  have hyη : y.asIdeal = Ideal.comap j η.asIdeal :=
    hj.symm.trans (congrArg (Ideal.comap j) hηideal).symm
  have hm : (residueFieldEquivOfEqBot K η.asIdeal hηideal : _ →+* K).comp
      (Ideal.ResidueField.map y.asIdeal η.asIdeal j hyη) =
      (algebraMap (X.residueField x') K).comp
        ((fromSpecStalk_residueEquiv x x' y hy).symm : _ →+* _) := by
    refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun s => ?_)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, Ideal.ResidueField.map_algebraMap,
      residueFieldEquivOfEqBot_algebraMap, hjK]
  have hη : (Spec.map (CommRingCat.ofHom j) ≫ X.fromSpecStalk x) η = x' := by
    show X.fromSpecStalk x (Spec.map (CommRingCat.ofHom j) η) = x'
    rw [hgen, hy]
  refine ⟨Spec.map (CommRingCat.ofHom j) ≫ X.fromSpecStalk x, hη,
    spec_map_fromSpecStalk_closedPoint x j,
    (specResidueFieldEquiv η).trans (residueFieldEquivOfEqBot K η.asIdeal hηideal), fun a => ?_⟩
  · have hb := DFunLike.congr_fun (specStalkResidueFieldMap_bridge (X.fromSpecStalk x) y hy
      (CommRingCat.ofHom j) η hgen) a
    refine (congrArg (residueFieldEquivOfEqBot K η.asIdeal hηideal) hb.symm).trans ?_
    have ha := DFunLike.congr_fun hm (fromSpecStalk_residueEquiv x x' y hy a)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at ha
    exact ha

/-- **Stacks Project, Tag 054F, part (2).** For a strict specialization and a
finitely generated extension `K` of the residue field at the generic point,
the realizing discrete valuation ring can be chosen so that its generic
residue field is isomorphic to `K` over that residue field. -/
@[stacks 054F "part (2)",
  ega "II 7.1.4" "special case",
  ega "II 7.1.9" "more general",
  ega "IV 15.5.2.2" "1°", sga "3 XV 3.3" "partial"]
theorem exists_dvr_morphism_of_specializes_with_residueField_equiv
    (X : Scheme.{u}) [IsLocallyNoetherian X] {x' x : X}
    (h : x' ⤳ x) (hne : x ≠ x')
    (K : Type u) [Field K] [Algebra (X.residueField x') K]
    [Algebra.EssFiniteType (X.residueField x') K] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (.of R) ⟶ X)
      (hη : f (genericPoint (Spec (.of R))) = x'),
      f (IsLocalRing.closedPoint R) = x ∧
        ∃ e : (Spec (.of R)).residueField (genericPoint (Spec (.of R))) ≃+* K,
          ∀ a : X.residueField x',
            e (f.residueFieldMap (genericPoint (Spec (.of R)))
              ((X.residueFieldCongr hη.symm).hom a)) =
              algebraMap (X.residueField x') K a := by
  let ρ : X.presheaf.stalk x →+* X.residueField x' :=
    ((X.presheaf.stalkSpecializes h) ≫ X.residue x').hom
  let z : Spec (.of (X.residueField x')) := IsLocalRing.closedPoint _
  let y : Spec (X.presheaf.stalk x) := Spec.map (CommRingCat.ofHom ρ) z
  have hρ : Spec.map (CommRingCat.ofHom ρ) ≫ X.fromSpecStalk x =
      X.fromSpecResidueField x' := by
    dsimp [ρ, Scheme.fromSpecResidueField]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  have hy : X.fromSpecStalk x y = x' := by
    show (Spec.map (CommRingCat.ofHom ρ) ≫ X.fromSpecStalk x) z = x'
    rw [hρ]
    exact Scheme.fromSpecResidueField_apply x' z
  obtain ⟨A, _, _, hDVR, _, _, j, _, hj, hjK⟩ :=
    exists_isDiscreteValuationRing_comap_bot_eq y.asIdeal
      (not_isField_quotient_of_fromSpecStalk_ne y (by rw [hy]; exact hne.symm))
      (fromSpecStalk_residueEquiv x x' y hy) K
  obtain ⟨f, hη, hclosed, e, he⟩ := exists_dvr_morphism_of_comap_bot_eq y hy K A j hj hjK
  exact ⟨A, inferInstance, inferInstance, hDVR, f, hη, hclosed, e, he⟩

/-- Every point of a scheme is the image of both the generic and the closed point of the
spectrum of a discrete valuation ring. -/
private theorem exists_dvr_morphism_genericPoint_closedPoint_eq (X : Scheme.{u}) (x : X) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (.of R) ⟶ X),
      f (genericPoint (Spec (.of R))) = x ∧
        f (IsLocalRing.closedPoint R) = x := by
  let S := X.presheaf.stalk x
  let k := X.residueField x
  let P : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k)}
  have hprime : P.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.irreducible_X.prime
  let R := Localization.AtPrime P
  let : IsLocalization.AtPrime R P := inferInstance
  have hP : P ≠ ⊥ := fun h => Polynomial.X_ne_zero (Ideal.span_singleton_eq_bot.mp h)
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (Polynomial k) hP R
  let : Algebra k (Polynomial k) := inferInstance
  let : Algebra k R := Algebra.compHom R (algebraMap k (Polynomial k))
  let φ : S →+* R := ((algebraMap k R).comp (X.residue x).hom)
  have hresLocal : IsLocalHom (X.residue x).hom :=
    IsLocalHom.of_surjective _ (X.residue_surjective x)
  have hfieldLocal : IsLocalHom (algebraMap k R) :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr (by rintro rfl; simp at ha)⟩
  have hloc : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal S := by
    ext s
    show φ s = 0 ↔ s ∈ IsLocalRing.maximalIdeal S
    constructor
    · intro hs
      have hres : (X.residue x).hom s = 0 := (algebraMap k R).injective (by simpa [φ] using hs)
      exact (IsLocalRing.residue_eq_zero_iff s).mp hres
    · intro hs
      have hres : (X.residue x).hom s = 0 := (IsLocalRing.residue_eq_zero_iff s).mpr hs
      simp [φ, hres]
  let f : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hgeneric : PrimeSpectrum.comap φ (⊥ : PrimeSpectrum R) = IsLocalRing.closedPoint S :=
    PrimeSpectrum.ext hker
  have hη : f (genericPoint (Spec (.of R))) = x := by
    show X.fromSpecStalk x (PrimeSpectrum.comap φ (genericPoint (Spec (.of R)))) = x
    rw [AlgebraicGeometry.genericPoint_eq_bot_of_affine, hgeneric,
      Scheme.fromSpecStalk_closedPoint]
  exact ⟨R, inferInstance, inferInstance, inferInstance, f, hη,
    spec_map_fromSpecStalk_closedPoint x φ⟩

/-- **Stacks Project, Tag 054F, part (1).** A specialization of points on a
locally Noetherian scheme is the image of the generic-to-closed specialization
on the spectrum of a discrete valuation ring. -/
@[stacks 054F "part (1)"]
theorem exists_dvr_morphism_of_specializes (X : Scheme.{u}) [IsLocallyNoetherian X]
    {x' x : X} (h : x' ⤳ x) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (.of R) ⟶ X),
      f (genericPoint (Spec (.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x := by
  obtain hxx' | hne := eq_or_ne x x'
  · subst x'
    exact exists_dvr_morphism_genericPoint_closedPoint_eq X x
  · obtain ⟨R, hR, hDom, hDVR, f, hη, hclosed, -⟩ :=
      exists_dvr_morphism_of_specializes_with_residueField_equiv X h hne
        (X.residueField x')
    exact ⟨R, hR, hDom, hDVR, f, hη, hclosed⟩

end AlgebraicGeometry

end

module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.IntegralClosure.Pi

/-!
# Integral closures after an algebraic base extension

Let `A → B` be an extension of discrete valuation rings with fraction fields `K → L`, and suppose
that `B` is essentially of finite type over `A`. For an algebraic field extension `K'/K`, form the
reduced tensor product `L' = (L ⊗[K] K')ᵣₑd`. If the integral closure `A'` of `A` in `K'` is
Noetherian, then so is the integral closure `B'` of `B` in `L'`. The induced map
`Spec(B') → Spec(A')` is surjective, and all of its residue field extensions are essentially of
finite type.

## Main results

* `IsDiscreteValuationRing.integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective`:
  Noetherianity, surjectivity on spectra, and finite generation of the residue field extensions
  after an algebraic base extension.

## Implementation notes

The reduction of a ring `R` is represented by `R ⧸ nilradical R`. Since the canonical algebra
structure from the first integral closure to the second is not an inferred instance, the result
supplies its ring homomorphism and characterizes it by its composite with the inclusion into the
reduced tensor product.

The Noetherianity and quasi-finiteness statements are both reduced to the case of a field: the
reduced tensor product is an Artinian reduced ring, hence a finite product of fields, and in each
factor the image of `B ⊗[A] A'` has that field as its fraction field. Integral closure commutes
with finite products (`integralClosurePiEquiv`), so the two properties can be assembled
coordinatewise from the Dedekind-domain statement for a one-dimensional Noetherian base.

Surjectivity on spectra factors as the base change `Spec(B ⊗[A] A') → Spec(A')`, which is
surjective because `A → B` is faithfully flat, followed by the integral map
`B ⊗[A] A' → B'`, whose kernel is nil; an integral map with nil kernel is surjective on spectra
because it is both closed and dominant. Residue field extensions being essentially of finite type
is not `RingHom.FiniteType`: a rational function field is finitely generated as a field but not as
an algebra, as `ratFunc_not_finiteType` records.

## References

* [Stacks Project, Tag 09IH](https://stacks.math.columbia.edu/tag/09IH)
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

universe uA uB uK uL v

namespace IsDiscreteValuationRing

/-- An algebraic base change of a field extension essentially of finite type has Artinian
reduction. -/
theorem reducedTensorProduct_isArtinian
    (K : Type uK) (L : Type uL) (K' : Type v)
    [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K'] :
    IsArtinianRing ((L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')) := by
  let T := L ⊗[K] K'
  have : IsNoetherianRing (K' ⊗[K] L) :=
    Algebra.EssFiniteType.isNoetherianRing K' _
  have : IsNoetherianRing T :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm K L K').toRingEquiv.symm
  let R := T ⧸ nilradical T
  have : IsNoetherianRing R := inferInstance
  have : Algebra.IsIntegral L T := Algebra.IsIntegral.tensorProduct K L K'
  have : Algebra.IsIntegral L R :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ L (nilradical T))
      (by exact Ideal.Quotient.mk_surjective)
  have : Ring.KrullDimLE 0 R := Ring.KrullDimLE.mk₀ fun I hI => by
    let : I.IsPrime := hI
    have hcomap : (I.comap (algebraMap L R)).IsMaximal := by infer_instance
    exact Ideal.IsIntegral.isMaximal_of_isMaximal_comap I hcomap
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- An integral algebra has no larger Krull dimension than its base. -/
private theorem krullDimLE_one_of_isIntegral
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Ring.KrullDimLE 1 R] : Ring.KrullDimLE 1 S :=
  Ring.krullDimLE_iff.mpr <| (Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R))

/-- The algebraic field extension is the fraction field of the integral closure. -/
private theorem integralClosure_isFractionRing_of_algebraic
    (A : Type uA) (K : Type uK) (K' : Type v)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K']
    [Algebra A K'] [IsScalarTower A K K'] :
    IsFractionRing (integralClosure A K') K' := by
  have : Algebra.IsAlgebraic A K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := K')).mpr inferInstance
  apply integralClosure.isFractionRing_of_algebraic
  intro x hx
  apply IsFractionRing.injective A K
  exact (algebraMap K K').injective (by
    simpa only [IsScalarTower.algebraMap_apply A K K', map_zero] using hx)

private noncomputable def baseChangeMap
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K' : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [Field L] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] :
    (B ⊗[A] integralClosure A K') →+*
      ((L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')) :=
  (Ideal.Quotient.mk (nilradical (L ⊗[K] K'))).comp
    (Algebra.TensorProduct.mapRingHom
      (algebraMap A K) (algebraMap B L) (integralClosure A K').val
      (by
        ext x
        exact (IsScalarTower.algebraMap_apply A B L x).symm.trans
          (IsScalarTower.algebraMap_apply A K L x))
      (by
        ext x
        exact IsScalarTower.algebraMap_apply A K K' x))

private lemma baseChangeMap_tmul
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K' : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [Field L] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    (b : B) (a : integralClosure A K') :
    baseChangeMap A B K L K' (b ⊗ₜ[A] a) =
      Ideal.Quotient.mk (nilradical (L ⊗[K] K')) (algebraMap B L b ⊗ₜ[K] (a : K')) := by
  simp only [baseChangeMap, RingHom.comp_apply, Algebra.TensorProduct.mapRingHom_tmul]
  rfl

private noncomputable def rightMap
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [Field L] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (K' : Type v) [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] :
    K' →ₐ[A] ((L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')) :=
  (Ideal.Quotient.mkₐ A (nilradical (L ⊗[K] K'))).comp
    ((Algebra.TensorProduct.includeRight : K' →ₐ[K] L ⊗[K] K').restrictScalars A)

private lemma rightMap_apply
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [Field L] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (K' : Type v) [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    (x : K') :
    rightMap A B K L K' x = algebraMap (L ⊗[K] K') ((L ⊗[K] K') ⧸
      nilradical (L ⊗[K] K')) (Algebra.TensorProduct.includeRight x) := rfl

/-- The range of a map out of a one-dimensional Noetherian integral algebra is again one-dimensional
Noetherian and integral. -/
private theorem range_isNoetherian_and_dimensionLEOne_and_isIntegral
    {B C F : Type*} [CommRing B] [CommRing C] [Field F] [Algebra B C] [Algebra B F]
    [Algebra.IsIntegral B C] [IsNoetherianRing C] [Ring.KrullDimLE 1 C] (f : C →ₐ[B] F) :
    IsNoetherianRing f.range ∧ Ring.DimensionLEOne f.range ∧ Algebra.IsIntegral B f.range := by
  have hs := f.rangeRestrict_surjective
  have : Ring.KrullDimLE 1 f.range := Ring.krullDimLE_iff.mpr <|
    (ringKrullDim_le_of_surjective f.rangeRestrict.toRingHom hs).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 C))
  exact ⟨isNoetherianRing_of_surjective C _ f.rangeRestrict.toRingHom hs,
    ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩, Algebra.IsIntegral.of_surjective f.rangeRestrict hs⟩

/-- Integral closure in `F` over `B` agrees with that over an integral `B`-subalgebra `D` of `F`. -/
private noncomputable def integralClosureSubalgebraEquiv
    (B F : Type*) [CommRing B] [CommRing F] [Algebra B F] (D : Subalgebra B F)
    [Algebra.IsIntegral B D] : integralClosure B F ≃ₐ[B] integralClosure D F :=
  have he : (integralClosure B F).toSubring = (integralClosure D F).toSubring := by
    ext x
    exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans (R := B) x hx⟩
  { __ := RingEquiv.subringCongr he, commutes' _ := rfl }

/-- The integral closure of a reduced Artinian algebra is the product of the integral closures of
its residue fields. -/
private noncomputable def integralClosureArtinianEquiv
    (B R : Type*) [CommRing B] [CommRing R] [Algebra B R] [IsArtinianRing R] [IsReduced R] :
    integralClosure B R ≃ₐ[B] ∀ m : MaximalSpectrum R, integralClosure B (R ⧸ m.asIdeal) :=
  (((IsArtinianRing.equivPi R).restrictScalars B).mapIntegralClosure).trans
    (integralClosurePiEquiv B fun m : MaximalSpectrum R => R ⧸ m.asIdeal)

private theorem integralClosure_isNoetherian_of_fractionRing_range
    (B C F : Type*) [CommRing B] [CommRing C] [Field F]
    [Algebra B C] [Algebra C F] [Algebra B F] [IsScalarTower B C F]
    [Algebra.IsIntegral B C] [IsNoetherianRing C] [Ring.KrullDimLE 1 C]
    [IsFractionRing (IsScalarTower.toAlgHom B C F).range F] :
    IsNoetherianRing (integralClosure B F) := by
  let f := IsScalarTower.toAlgHom B C F
  let D := f.range
  obtain ⟨_, _, _⟩ := range_isNoetherian_and_dimensionLEOne_and_isIntegral f
  have hD := IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
    D F F (integralClosure D F)
  have : IsDedekindDomain (integralClosure D F) := hD.1
  exact isNoetherianRing_of_ringEquiv (integralClosure D F)
    (integralClosureSubalgebraEquiv B F D).toRingEquiv.symm

private theorem integralClosure_isNoetherian_of_isArtinian
    (B C R : Type*) [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra C R] [Algebra B R] [IsScalarTower B C R]
    [Algebra.IsIntegral B C] [IsNoetherianRing C] [Ring.KrullDimLE 1 C]
    [IsArtinianRing R] [IsReduced R]
    (hfrac : ∀ m : MaximalSpectrum R,
      IsFractionRing (IsScalarTower.toAlgHom B C (R ⧸ m.asIdeal)).range (R ⧸ m.asIdeal)) :
    IsNoetherianRing (integralClosure B R) := by
  let F (m : MaximalSpectrum R) := R ⧸ m.asIdeal
  let (m : MaximalSpectrum R) : Field (F m) := Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum R) : IsNoetherianRing (integralClosure B (F m)) := by
    have := hfrac m
    exact integralClosure_isNoetherian_of_fractionRing_range B C (F m)
  exact isNoetherianRing_of_ringEquiv (∀ m, integralClosure B (F m))
    (integralClosureArtinianEquiv B R).toRingEquiv.symm

private theorem isFractionRing_of_closure_eq_top
    {F : Type*} [Field F] (D : Subring F) (hD : Subfield.closure (D : Set F) = ⊤) :
    IsFractionRing D F := by
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ Subfield.closure (D : Set F) := hD ▸ Subfield.mem_top x
  obtain ⟨y, hy, z, hz, he⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  exact ⟨⟨y, hy⟩, ⟨z, hz⟩, he.symm⟩

private theorem isFractionRing_range_of_tensorProduct
    (B D C K L E F : Type*)
    [CommRing B] [IsDomain B] [CommRing D] [IsDomain D] [CommRing C]
    [Field K] [Field L] [Field E] [Field F]
    [Algebra K L] [Algebra K E]
    [Algebra B L] [IsFractionRing B L] [Algebra D E] [IsFractionRing D E]
    (i : B →+* C) (j : D →+* C) (f : C →+* F) (g : L ⊗[K] E →+* F)
    (hg : Function.Surjective g)
    (hi : (g.comp (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E).toRingHom).comp
      (algebraMap B L) = f.comp i)
    (hj : (g.comp (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E).toRingHom).comp
      (algebraMap D E) = f.comp j) :
    IsFractionRing f.range F := by
  apply isFractionRing_of_closure_eq_top
  let S := Subfield.closure (f.range : Set F)
  have hL :
      (g.comp (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E).toRingHom).fieldRange ≤ S := by
    rw [IsFractionRing.ringHom_fieldRange_eq_of_comp_eq hi]
    apply Subfield.closure_le.mpr
    rintro x ⟨b, rfl⟩
    exact Subfield.subset_closure ⟨i b, rfl⟩
  have hE :
      (g.comp
        (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E).toRingHom).fieldRange ≤ S := by
    rw [IsFractionRing.ringHom_fieldRange_eq_of_comp_eq hj]
    apply Subfield.closure_le.mpr
    rintro x ⟨d, rfl⟩
    exact Subfield.subset_closure ⟨j d, rfl⟩
  have hmem (t : L ⊗[K] E) : g t ∈ S := by
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using S.zero_mem
    | tmul l e =>
        have h : l ⊗ₜ[K] e =
            (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) l *
              (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) e := by
          simp
        rw [h, map_mul]
        exact S.mul_mem (hL ⟨l, rfl⟩) (hE ⟨e, rfl⟩)
    | add x y hx hy => simpa only [map_add] using S.add_mem hx hy
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hg x
  exact hmem t

/-- A rational function field is not finitely generated as an algebra over its
coefficient field. In particular, finite generation of a residue field extension
as a field does not imply `RingHom.FiniteType`. -/
private theorem ratFunc_not_finiteType (k : Type*) [Field k] :
    ¬ (algebraMap k (RatFunc k)).FiniteType := by
  intro h
  have : Algebra.FiniteType k (RatFunc k) := RingHom.finiteType_algebraMap.mp h
  have : Module.Finite k (RatFunc k) :=
    finite_of_finite_type_of_isJacobsonRing k (RatFunc k)
  exact RatFunc.transcendental_X (Algebra.IsAlgebraic.isAlgebraic (RatFunc.X : RatFunc k))

/-- Quasi-finiteness is preserved by finite products. -/
private theorem quasiFinite_pi (R : Type*) [CommRing R] (ι : Type*) [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Algebra.QuasiFinite R (S i)] : Algebra.QuasiFinite R (∀ i, S i) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  intro p hp
  let e := Algebra.TensorProduct.piRight R p.ResidueField p.ResidueField S
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- Normalization in the fraction field of a quotient of a one-dimensional
Noetherian ring is quasi-finite over that ring. -/
private theorem integralClosure_quasiFinite_of_fractionRing_range
    (R F : Type*) [CommRing R] [Field F] [Algebra R F]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [IsFractionRing (Algebra.ofId R F).range F] :
    Algebra.QuasiFinite R (integralClosure R F) := by
  let f := Algebra.ofId R F
  let D := f.range
  obtain ⟨_, _, _⟩ := range_isNoetherian_and_dimensionLEOne_and_isIntegral f
  have : Algebra.QuasiFinite D (integralClosure D F) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      D F F (integralClosure D F)).2.2
  have : Module.Finite R D :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  have : Algebra.QuasiFinite R (integralClosure D F) :=
    .trans R D (integralClosure D F)
  exact (Algebra.QuasiFinite.iff_of_algEquiv (integralClosureSubalgebraEquiv R F D)).mpr
    inferInstance

/-- Normalization in a reduced Artinian algebra is quasi-finite when its field
components are fraction fields of quotients of the base. -/
private theorem integralClosure_quasiFinite_of_isArtinian
    (C R : Type*) [CommRing C] [CommRing R] [Algebra C R]
    [IsNoetherianRing C] [Ring.KrullDimLE 1 C] [IsArtinianRing R] [IsReduced R]
    (hfrac : ∀ m : MaximalSpectrum R,
      IsFractionRing (Algebra.ofId C (R ⧸ m.asIdeal)).range (R ⧸ m.asIdeal)) :
    Algebra.QuasiFinite C (integralClosure C R) := by
  let F (m : MaximalSpectrum R) := R ⧸ m.asIdeal
  let (m : MaximalSpectrum R) : Field (F m) := Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum R) : Algebra.QuasiFinite C (integralClosure C (F m)) := by
    have := hfrac m
    exact integralClosure_quasiFinite_of_fractionRing_range C (F m)
  have : Algebra.QuasiFinite C (∀ m, integralClosure C (F m)) :=
    quasiFinite_pi C (MaximalSpectrum R) _
  exact (Algebra.QuasiFinite.iff_of_algEquiv (integralClosureArtinianEquiv C R)).mpr
    inferInstance

/-- An integral map with nil kernel is surjective on prime spectra. -/
private theorem comap_surjective_of_isIntegral_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hker : RingHom.ker f ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  have hd := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr hker
  have hc : IsClosed (Set.range (PrimeSpectrum.comap f)) := by
    simpa using PrimeSpectrum.isClosedMap_comap_of_isIntegral f hf Set.univ isClosed_univ
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans hd.closure_range)

private theorem residueFieldMap_essFiniteType_of_quasiFinite
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.QuasiFinite) (q : PrimeSpectrum S) :
    (Ideal.ResidueField.map (q.asIdeal.comap f) q.asIdeal f rfl).EssFiniteType := by
  let := f.toAlgebra
  have : Algebra.QuasiFinite R S := hf
  let p := q.asIdeal.under R
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have : Module.Finite p.ResidueField q.asIdeal.ResidueField := inferInstance
  show (algebraMap p.ResidueField q.asIdeal.ResidueField).EssFiniteType
  exact RingHom.essFiniteType_algebraMap.mpr inferInstance

private theorem residueFieldMap_essFiniteType_of_comp_quasiFinite
    {R C S : Type*} [CommRing R] [CommRing C] [CommRing S]
    (f : R →+* C) (g : C →+* S) (hf : f.EssFiniteType) (hg : g.QuasiFinite)
    (q : PrimeSpectrum S) :
    (Ideal.ResidueField.map (q.asIdeal.comap (g.comp f)) q.asIdeal
      (g.comp f) rfl).EssFiniteType := by
  let p := q.asIdeal.comap g
  let j := Ideal.ResidueField.map p q.asIdeal g rfl
  apply RingHom.EssFiniteType.of_comp (algebraMap R (q.asIdeal.comap (g.comp f)).ResidueField)
  have hj : j.EssFiniteType := residueFieldMap_essFiniteType_of_quasiFinite g hg q
  have hc : (algebraMap C p.ResidueField).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr inferInstance
  convert (hf.comp hc).comp hj using 1
  ext r
  simp [j, Ideal.ResidueField.map_algebraMap]

/-- The base-change map into the reduced tensor product has nil kernel. -/
private theorem baseChangeMap_ker_le_nilradical
    (A B K L K' : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Module.Flat A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] :
    RingHom.ker (baseChangeMap A B K L K') ≤
      nilradical (B ⊗[A] integralClosure A K') := by
  have : Module.Flat A K := IsLocalization.flat K A⁰
  have : Module.Flat A K' := Module.Flat.trans A K K'
  let h := Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L)
    (integralClosure A K').val
  let e := (IsLocalization.algebraTensorEquiv A⁰ K L K').symm
  let g := e.toRingHom.comp h.toRingHom
  have hh : Function.Injective h :=
    TensorProduct.map_injective_of_flat_flat'
      (IsScalarTower.toAlgHom A B L).toLinearMap (integralClosure A K').val.toLinearMap
      (IsFractionRing.injective B L) Subtype.val_injective
  have hg : Function.Injective g := e.injective.comp hh
  have he : baseChangeMap A B K L K' =
      (Ideal.Quotient.mk (nilradical (L ⊗[K] K'))).comp g := by
    ext x <;> simp [baseChangeMap, g, h, e, IsLocalization.algebraTensorEquiv,
      Algebra.TensorProduct.equivOfCompatibleSMul, Algebra.TensorProduct.mapRingHom_tmul]
  intro x hx
  rw [he] at hx
  exact mem_nilradical.mpr ((IsNilpotent.map_iff hg).mp
    (mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)))

/-- Essential finite type is preserved by base change on either tensor factor. -/
private theorem tensorProduct_includeRight_essFiniteType
    (A B D : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [Algebra.EssFiniteType A B] :
    (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D).toRingHom.EssFiniteType := by
  let : Algebra D (B ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (B ⊗[A] D) ≃ₐ[D] (D ⊗[A] B) :=
    { __ := Algebra.TensorProduct.comm A B D, commutes' _ := rfl }
  exact RingHom.essFiniteType_algebraMap.mpr
    ((Algebra.EssFiniteType.iff_of_algEquiv e).mpr inferInstance)

/-- A faithfully flat base change is surjective on prime spectra. -/
private theorem tensorProduct_includeRight_comap_surjective
    (A B D : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [Module.FaithfullyFlat A B] :
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D).toRingHom) := by
  let : Algebra D (B ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (B ⊗[A] D) ≃ₐ[D] (D ⊗[A] B) :=
    { __ := Algebra.TensorProduct.comm A B D, commutes' _ := rfl }
  have : Module.FaithfullyFlat D (B ⊗[A] D) :=
    Module.FaithfullyFlat.of_linearEquiv D (D ⊗[A] B) e.toLinearEquiv
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- Let `A → B` be an essentially finite type extension of discrete valuation
rings with fraction fields `K → L`. If `K'/K` is algebraic and the integral
closure `A'` of `A` in `K'` is Noetherian, then the integral closure `B'` of `B`
in the reduction of `L ⊗[K] K'` is Noetherian. The canonical map
`Spec(B') → Spec(A')` is surjective and all corresponding residue field
extensions are finitely generated. -/
@[stacks 09IH]
theorem integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.EssFiniteType A B]
    (K' : Type v) [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K']
    [Algebra A K'] [IsScalarTower A K K']
    [IsNoetherianRing (integralClosure A K')] :
    let L' := (L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')
    let A' := integralClosure A K'
    let B' := integralClosure B L'
    IsNoetherianRing B' ∧
      ∃ f : A' →+* B',
        (∀ x : A',
          ((B').val (f x) : L') =
            algebraMap (L ⊗[K] K') L'
              (Algebra.TensorProduct.includeRight (x : K'))) ∧
        Function.Surjective (PrimeSpectrum.comap f) ∧
        ∀ q : PrimeSpectrum B',
          (Ideal.ResidueField.map (q.asIdeal.comap f) q.asIdeal f rfl).EssFiniteType := by
  classical
  let A' := integralClosure A K'
  let T := L ⊗[K] K'
  let R := T ⧸ nilradical T
  let C := B ⊗[A] A'
  let E := integralClosure B R
  let f := baseChangeMap A B K L K'
  let : Algebra C R := f.toAlgebra
  have hf_left (b : B) : f (algebraMap B C b) = algebraMap B R b := by
    show f (b ⊗ₜ[A] (1 : A')) =
      Ideal.Quotient.mk (nilradical T) ((algebraMap B L b) ⊗ₜ[K] (1 : K'))
    exact baseChangeMap_tmul A B K L K' b 1
  have hf_right (a : A') : f ((1 : B) ⊗ₜ[A] a) =
      algebraMap T R (Algebra.TensorProduct.includeRight (a : K')) := by
    rw [baseChangeMap_tmul, map_one]
    rfl
  have : IsScalarTower B C R := IsScalarTower.of_algebraMap_eq fun b => (hf_left b).symm
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tensorProduct A B A'
  have : Ring.KrullDimLE 1 C := krullDimLE_one_of_isIntegral B C
  have : IsNoetherianRing (A' ⊗[A] B) := Algebra.EssFiniteType.isNoetherianRing A' _
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv (A' ⊗[A] B)
    (Algebra.TensorProduct.comm A A' B).toRingEquiv
  have : Algebra.EssFiniteType B L := .of_isLocalization L B⁰
  have : Algebra.EssFiniteType A L := .comp A B L
  have : Algebra.EssFiniteType K L := .of_comp A K L
  have : IsArtinianRing R := reducedTensorProduct_isArtinian K L K'
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  have : IsFractionRing A' K' := integralClosure_isFractionRing_of_algebraic A K K'
  have hfrac (m : MaximalSpectrum R) :
      IsFractionRing (IsScalarTower.toAlgHom B C (R ⧸ m.asIdeal)).range
        (R ⧸ m.asIdeal) := by
    let : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let g := (Ideal.Quotient.mk m.asIdeal).comp (Ideal.Quotient.mk (nilradical T))
    have hg : Function.Surjective g :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    show IsFractionRing (algebraMap C (R ⧸ m.asIdeal)).range (R ⧸ m.asIdeal)
    apply isFractionRing_range_of_tensorProduct B A' C K L K' _
      (algebraMap B C) Algebra.TensorProduct.includeRight.toRingHom
      (algebraMap C (R ⧸ m.asIdeal)) g hg
    · ext b
      show Ideal.Quotient.mk m.asIdeal (algebraMap B R b) =
        Ideal.Quotient.mk m.asIdeal (f (algebraMap B C b))
      rw [hf_left]
    · ext a
      exact congrArg (Ideal.Quotient.mk m.asIdeal) (hf_right a).symm
  have hnoeth : IsNoetherianRing E :=
    integralClosure_isNoetherian_of_isArtinian B C R hfrac
  refine ⟨hnoeth, ?_⟩
  let i : C →ₐ[B] E := IsIntegralClosure.lift B E R
  have hif (x : C) : algebraMap E R (i x) = f x := IsIntegralClosure.algebraMap_lift B E R x
  let : Algebra C E := i.toRingHom.toAlgebra
  have : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have : IsScalarTower C E R := IsScalarTower.of_algebraMap_eq fun c =>
    (IsIntegralClosure.algebraMap_lift B E R c).symm
  have : IsIntegralClosure E C R := by
    refine ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, isIntegral_trans (R := B) x hx⟩, rfl⟩, ?_⟩⟩
    rintro ⟨x, rfl⟩
    exact x.property.tower_top
  have : Algebra.QuasiFinite C (integralClosure C R) :=
    integralClosure_quasiFinite_of_isArtinian C R hfrac
  have hqf : Algebra.QuasiFinite C E :=
    (Algebra.QuasiFinite.iff_of_algEquiv (R := C) (S := E) (T := integralClosure C R)
      (IsIntegralClosure.equiv C E R (integralClosure C R))).mpr inferInstance
  let j : A' →+* C := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨i.toRingHom.comp j, ?_, ?_, ?_⟩
  · intro a
    exact (hif (j a)).trans (hf_right a)
  · have hi : i.toRingHom.IsIntegral :=
      algebraMap_isIntegral_iff.mpr (IsIntegralClosure.isIntegral_algebra C R)
    have hker : RingHom.ker i.toRingHom ≤ nilradical C := by
      intro x hx
      apply baseChangeMap_ker_le_nilradical A B K L K'
      show f x = 0
      rw [← hif, show i x = 0 from hx, map_zero]
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact (tensorProduct_includeRight_comap_surjective A B A').comp
      (comap_surjective_of_isIntegral_of_ker_le_nilradical i.toRingHom hi hker)
  · exact residueFieldMap_essFiniteType_of_comp_quasiFinite j i.toRingHom
      (tensorProduct_includeRight_essFiniteType A B A') hqf

end IsDiscreteValuationRing

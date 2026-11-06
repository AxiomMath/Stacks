module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FieldExtensionStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.FieldTheory.InseparableDegreeTensorLength
public import StacksFrontier.FieldTheory.SeparableAlgebraic.TensorProduct
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Ramification on passing to an algebraic closure

For a smooth curve over a field, the ramification index at a closed point after extending
scalars to an algebraic closure is the inseparable degree of the original residue field.

## Main results

* `AlgebraicGeometry.ramificationIdx_baseChange_algClosure_eq_finInsepDegree` computes this
  ramification index.

## Implementation notes

The base-changed curve is the categorical pullback along the map of spectra induced by the
chosen algebraic closure. The algebra structures on the residue field and on the two local
rings are the canonical maps induced by the curve morphism and by the pullback projection.
The numerical ramification index is
`Stacks.DiscreteValuationRing.Ramification.ramificationIdx`, which is defined for local rings
and agrees with the discrete-valuation-ring ramification index in this setting.

## References

* [Stacks Project, Tag 0C1G](https://stacks.math.columbia.edu/tag/0C1G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### General lemmas on lengths and localizations -/

/-- If `S` is a localization of `A` at a prime `p` and `J ≤ p`, then `S ⧸ J·S` is the
localization of `A ⧸ J` at a prime; the quotient is transported along a chosen presentation
`e` of `A ⧸ J`. -/
private lemma exists_ringEquiv_quotient_localization
    {A : Type u} (S : Type u) {C : Type u} [CommRing A] [CommRing S] [CommRing C] [Algebra A S]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p]
    (J : Ideal A) (hJ : J ≤ p) (e : (A ⧸ J) ≃+* C) :
    ∃ (t : Ideal C) (_ : t.IsPrime),
      Nonempty ((S ⧸ Ideal.map (algebraMap A S) J) ≃+* Localization.AtPrime t) := by
  let q : Ideal (A ⧸ J) := Ideal.map (Ideal.Quotient.mk J) p
  have : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hJ
  have hq : Ideal.comap (Ideal.Quotient.mk J) q = p := Ideal.comap_map_mk hJ
  have hm : Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl = q.primeCompl := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    exact ⟨fun ⟨b, hb, hab⟩ => hab ▸ (by simpa [← hq] using (hb : b ∉ p)),
      fun ha => ⟨a, by simpa [← hq] using ha, rfl⟩⟩
  have : IsLocalization q.primeCompl (S ⧸ Ideal.map (algebraMap A S) J) := by
    rw [← hm]; infer_instance
  let t : Ideal C := Ideal.comap e.symm.toRingHom q
  have ht : q = Ideal.comap e.toRingHom t := by ext z; simp [t]
  exact ⟨t, Ideal.comap_isPrime _ _,
    ⟨((IsLocalization.algEquiv q.primeCompl (S ⧸ Ideal.map (algebraMap A S) J)
        (Localization.AtPrime q)).toRingEquiv).trans (Localization.localRingEquiv q t e ht)⟩⟩

/-! ### The special fibre of a local ring after extending the ground field -/

/-- The special fibre of the map of local rings induced by a base change along a field
extension is a localization of `κ(x) ⊗_k K`. -/
private lemma exists_specialFibre_localization (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    letI : Algebra k (X.residueField
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)) :=
      (fieldToResidue f _).hom.toAlgebra
    ∃ (t : Ideal (X.residueField
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) ⊗[k] K))
      (_ : t.IsPrime),
      Nonempty (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
            Scheme.{u}).presheaf.stalk y ⧸
          Ideal.map ((pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
            (IsLocalRing.maximalIdeal (X.presheaf.stalk
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y)))) ≃+*
        Localization.AtPrime t) := by
  set x := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y
  obtain ⟨θ, ψ, φ, hθl, hθr, hψl, hψr, hφl, hφr, hθψ, hloc⟩ :=
    stalkOfBaseChange_isLocalization f x y rfl
  simp only at hφl hθψ hloc
  have hφl' : pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K)) ≫ φ =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y := by
    refine hφl.trans ?_
    simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl]
    exact Category.id_comp _
  let : Algebra k ↥(X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  let : Algebra ↥(stalkBaseChangeRing (K := K) f x)
      ↥((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) := φ.hom.toAlgebra
  have : (RingHom.ker ψ.hom).IsPrime := RingHom.ker_isPrime _
  have : (Ideal.comap θ.hom (RingHom.ker ψ.hom)).IsPrime := Ideal.comap_isPrime _ _
  have hlocP : IsLocalization.AtPrime
      ↥((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) (Ideal.comap θ.hom (RingHom.ker ψ.hom)) := hloc
  set ι : X.presheaf.stalk x ⟶ stalkBaseChangeRing (K := K) f x :=
    pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K : k →+* K))
  set J : Ideal ↥(stalkBaseChangeRing (K := K) f x) :=
    Ideal.map ι.hom (IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x)) with hJdef
  have hJp : J ≤ Ideal.comap θ.hom (RingHom.ker ψ.hom) := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro z hz
    change ψ.hom (θ.hom (ι.hom z)) = 0
    have h1 : ψ.hom (θ.hom (ι.hom z)) =
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).residue y).hom (φ.hom (ι.hom z)) :=
      congrArg (fun m : stalkBaseChangeRing (K := K) f x ⟶
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).residueField y => m.hom (ι.hom z)) hθψ
    have h2 : φ.hom (ι.hom z) =
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom z :=
      congrArg (fun m : X.presheaf.stalk x ⟶
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y => m.hom z) hφl'
    rw [h1, h2]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ((IsLocalRing.mem_maximalIdeal _).mpr ?_)
    exact fun hu => (IsLocalRing.mem_maximalIdeal z).mp hz (isUnit_of_map_unit _ _ hu)
  have hpo := CommRingCat.isPushout_tensorProduct k ↥(X.presheaf.stalk x) K
  let eA : ↥(X.presheaf.stalk x) ⊗[k] K ≃+* ↥(stalkBaseChangeRing (K := K) f x) :=
    hpo.isoPushout.commRingCatIsoToRingEquiv
  have hinl : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := ↥(X.presheaf.stalk x)) (B := K)) ≫
      hpo.isoPushout.hom = ι := hpo.inl_isoPushout_hom
  set J' : Ideal (↥(X.presheaf.stalk x) ⊗[k] K) :=
    Ideal.map (algebraMap ↥(X.presheaf.stalk x) (↥(X.presheaf.stalk x) ⊗[k] K))
      (IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x)) with hJ'def
  have hJeq : J = Ideal.map eA.toRingHom J' := by
    rw [hJdef, hJ'def, Ideal.map_map]
    congr 1
    exact (congrArg CommRingCat.Hom.hom hinl).symm
  let eQ :=
    (Ideal.quotientEquiv J' J eA hJeq).symm.trans
      (Algebra.TensorProduct.quotientTensorEquiv (R := k) k K ↥(X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x))).symm.toRingEquiv
  obtain ⟨t, htp, ⟨eFin⟩⟩ :=
    exists_ringEquiv_quotient_localization
      ↥((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y)
      (Ideal.comap θ.hom (RingHom.ker ψ.hom)) J hJp eQ
  refine ⟨t, htp, ⟨?_⟩⟩
  have hmapJ : Ideal.map (algebraMap ↥(stalkBaseChangeRing (K := K) f x)
        ↥((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y)) J =
      Ideal.map ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
        (IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x)) := by
    rw [hJdef, Ideal.map_map]
    congr 1
    exact congrArg CommRingCat.Hom.hom hφl'
  exact hmapJ ▸ eFin

/-! ### Ramification at a closed point of a smooth curve -/

/-- For a faithfully flat extension of discrete valuation rings, the ramification index is the
length of the special fibre. -/
private theorem ramificationIdx_eq_length_specialFibre (A B : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B] :
    (Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B : ℕ∞) =
      Module.length B (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) := by
  rw [Stacks.DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx
      A B,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- The image of a closed point of the base change along an algebraic closure is closed. -/
private theorem projection_image_isClosed (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (xbar : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hxbar : IsClosed ({xbar} : Set
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))) :
    IsClosed ({pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) xbar} : Set X) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIntegralHom g := IsIntegralHom.SpecMap_iff.mpr <| algebraMap_isIntegral_iff.mpr <|
    Algebra.isAlgebraic_iff_isIntegral.mp IsAlgClosure.isAlgebraic
  let p := pullback.fst f g
  have : IsIntegralHom p := inferInstance
  have : UniversallyClosed p := inferInstance
  rw [← Set.image_singleton]
  exact p.isClosedMap _ hxbar

/-- The local ring of a smooth scheme over a field at a point where it has dimension one is a
discrete valuation ring. -/
private theorem stalk_isDVR_of_smooth_of_ringKrullDim_eq_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hreg : IsLocallyNoetherian X ∧ ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    ((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field f)
  have hregdim : IsRegularLocalRing (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 := ⟨hreg.2 x, hdim⟩
  exact ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 3 1).mp hregdim

/-- The local ring of a smooth curve at a closed point is a discrete valuation ring. -/
private theorem stalk_isDVR_of_closed_point (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
  stalk_isDVR_of_smooth_of_ringKrullDim_eq_one k f x <| calc
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDimAt X x :=
      (topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx).symm
    _ = topologicalKrullDim X :=
      (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x).symm
    _ = 1 := (inferInstance : IsCurve k f).topologicalKrullDim_eq_one

/-- The residue field at a closed point of a scheme locally of finite type over a field is a
finite extension of that field. -/
@[ega "I 6.4.2" "necessity", sga "6 X 7.17.5" "partial"]
public theorem residueField_finite_of_closed_point (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have hclosedImmersion := isClosed_singleton_iff_isClosedImmersion.mp hx
    infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- The ramification index at a closed point of a smooth curve after extension to an algebraic
closure is the inseparable degree of the original residue field. -/
@[stacks 0C1G]
public theorem ramificationIdx_baseChange_algClosure_eq_finInsepDegree
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    (xbar : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hxbar : IsClosed ({xbar} : Set
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let x := p xbar
    letI : Algebra (X.presheaf.stalk x)
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk xbar) :=
      (p.stalkMap xbar).hom.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx (X.presheaf.stalk x)
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk xbar) =
      Field.finInsepDegree k (X.residueField x) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let x := p xbar
  let Y := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})
  let q : Y ⟶ Spec (.of K) := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hx : IsClosed ({x} : Set X) := projection_image_isClosed k K f xbar hxbar
  obtain ⟨hDomainA, hDvrA⟩ := stalk_isDVR_of_closed_point k f x hx
  let : IsDomain (X.presheaf.stalk x) := hDomainA
  let : IsDiscreteValuationRing (X.presheaf.stalk x) := hDvrA
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  let : Module.Finite k (X.residueField x) := residueField_finite_of_closed_point k f x hx
  have hdvrA : ∃ _ : IsDomain (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x) := ⟨inferInstance, inferInstance⟩
  have hregdimA : IsRegularLocalRing (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 :=
    ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 1 3).mp hdvrA
  have hdimB : ringKrullDim (Y.presheaf.stalk xbar) = 1 := by
    calc
      ringKrullDim (Y.presheaf.stalk xbar) = topologicalKrullDimAt Y xbar :=
        (topologicalKrullDimAt_eq_krullDimOfRing_stalk K Y q xbar hxbar).symm
      _ = topologicalKrullDimAt X x := topologicalKrullDimAt_baseChange_eq k K X f xbar
      _ = ringKrullDim (X.presheaf.stalk x) :=
        topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx
      _ = 1 := hregdimA.2
  obtain ⟨hDomainB, hDvrB⟩ := stalk_isDVR_of_smooth_of_ringKrullDim_eq_one K q xbar hdimB
  let : IsDomain (Y.presheaf.stalk xbar) := hDomainB
  let : IsDiscreteValuationRing (Y.presheaf.stalk xbar) := hDvrB
  let : Algebra (X.presheaf.stalk x) (Y.presheaf.stalk xbar) := (p.stalkMap xbar).hom.toAlgebra
  let : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) _)
  let : Module.Flat (X.presheaf.stalk x) (Y.presheaf.stalk xbar) :=
    AlgebraicGeometry.Flat.stalkMap p xbar
  let : IsLocalHom (algebraMap (X.presheaf.stalk x) (Y.presheaf.stalk xbar)) := by
    change IsLocalHom (p.stalkMap xbar).hom
    infer_instance
  let : FaithfulSMul (X.presheaf.stalk x) (Y.presheaf.stalk xbar) := inferInstance
  have he := ramificationIdx_eq_length_specialFibre (X.presheaf.stalk x) (Y.presheaf.stalk xbar)
  obtain ⟨t, htp, ⟨eSF⟩⟩ := exists_specialFibre_localization k K f xbar
  have : t.IsPrime := htp
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  calc
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx (X.presheaf.stalk x)
          (Y.presheaf.stalk xbar)
        = (Module.length (Y.presheaf.stalk xbar)
            (Y.presheaf.stalk xbar ⧸ Ideal.map (p.stalkMap xbar).hom
              (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).toNat := by
          simpa only [RingHom.algebraMap_toAlgebra, ENat.toNat_natCast] using congrArg ENat.toNat he
    _ = (Module.length (Y.presheaf.stalk xbar ⧸ Ideal.map (p.stalkMap xbar).hom
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
          (Y.presheaf.stalk xbar ⧸ Ideal.map (p.stalkMap xbar).hom
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).toNat :=
        congrArg ENat.toNat (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective)
    _ = (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat :=
        congrArg ENat.toNat (Module.length_self_eq_of_ringEquiv eSF)
    _ = Field.finInsepDegree k (X.residueField x) :=
        Field.length_atPrime_tensorAlgClosed_eq_finInsepDegree k (X.residueField x) K t

end AlgebraicGeometry

end

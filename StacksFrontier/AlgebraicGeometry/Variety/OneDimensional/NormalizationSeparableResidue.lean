module

public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Regular.RegularRingHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separable residue fields on the normalization of a one-dimensional point

Let `k` be a field, let `X` be locally of finite type over `k`, and let `x` be a point of `X`
whose local ring is reduced of dimension one. If every point of the normalization above `x` has
residue field separable over `k`, then `X` is geometrically reduced at `x`, and the normalization
is geometrically regular at every one of those points.

## Main results

* `AlgebraicGeometry.isGeometricallyReducedAt_of_normalization_residueField_isSeparable`: the
  scheme is geometrically reduced at the point.
* `AlgebraicGeometry.isGeometricallyRegularAt_normalization_of_residueField_isSeparable`: the
  normalization is geometrically regular above the point.

## Implementation notes

The separability hypothesis is phrased for each point of the normalization over `x` using the
`k`-algebra structure on its residue field induced by the structure morphism of the
normalization. The normalization is a normal locally Noetherian scheme, so its local rings at
those points are one-dimensional normal domains, hence discrete valuation rings; geometric
regularity then follows from separability of the residue field, and geometric reducedness of `X`
at `x` descends along the normalization.

## References

* [Stacks Project, Tag 0C3P](https://stacks.math.columbia.edu/tag/0C3P)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry


open CategoryTheory.Limits TopologicalSpace TensorProduct

private theorem isGeometricallyRegular_of_isRegularRing_charZero
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    [CharZero k] [IsRegularRing A] : Algebra.IsGeometricallyRegular k A := by
  refine ⟨(Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k A).mpr fun K _ _ _ _ => ?_⟩
  have hbij : Function.Bijective (algebraMap k K) :=
    ⟨(algebraMap k K).injective,
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K⟩
  let e : K ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k K) hbij).symm
  exact IsRegularRing.of_ringEquiv ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
    (Algebra.TensorProduct.lid k A)).toRingEquiv.symm

@[sga "1 II 5.9" "(i)"]
private theorem isGeometricallyRegular_of_isRegularLocalRing_residueField_isSeparable
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A]
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField A)) :
    Algebra.IsGeometricallyRegular k A := by
  obtain hchar | ⟨p, hp, hkp⟩ := CharP.exists' k
  · have : IsRegularRing A := ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp ‹_›
    exact isGeometricallyRegular_of_isRegularRing_charZero k A
  · have : Fact p.Prime := hp
    let m := IsLocalRing.maximalIdeal A
    let : TopologicalSpace k := ⊥
    have : DiscreteTopology k := ⟨rfl⟩
    let : TopologicalSpace A := m.adicTopology
    have : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
    have : IsLinearTopology A A := m.isLinearTopology
    exact (((formalSmoothness_maximalIdeal_characterizations k A).2 p).out 2 1).mp
      (isFormallySmooth_maximalIdeal_of_isRegularLocalRing (k := k) (A := A) hsep)

private theorem isRegularLocalRing_of_normal_isDomain_dim_le_one
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsDomain B]
    (hnormal : IsIntegrallyClosed B) (hdim : ringKrullDim B ≤ 1) :
    IsRegularLocalRing B := by
  by_cases hfield : IsField B
  · let : Field B := hfield.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr hdim
    have hdimone : ringKrullDim B = 1 :=
      (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain).2 ⟨hfield, fun a ha => by
        rw [Ideal.radical_eq_sInf]
        apply le_sInf
        intro J hJ
        have haJ : a ∈ J := hJ.1 (Ideal.subset_span (by simp))
        have hJne : J ≠ ⊥ := fun he => ha (by simpa [he] using haJ)
        exact (IsLocalRing.eq_maximalIdeal (hJ.2.isMaximal_of_ne_bot hJne)).ge⟩
    have hinput : IsNoetherianRing B ∧ IsLocalRing B ∧ IsDomain B ∧
        IsIntegrallyClosed B ∧ ringKrullDim B = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, hnormal, hdimone⟩
    have hout : IsRegularLocalRing B ∧ ringKrullDim B = 1 :=
      ((isDiscreteValuationRing_tfae B).out 5 3).mp hinput
    exact hout.1

private theorem ringKrullDim_stalk_le_of_isIntegralHom
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIntegralHom g] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (X.presheaf.stalk (g y)) := by
  obtain ⟨U, hU, hyU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (g y))
  let V := g ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage g
  have hyV : y ∈ V := hyU
  let p := hU.primeIdealOf ⟨g y, hyU⟩
  let q := hV.primeIdealOf ⟨y, hyV⟩
  let φ := (g.appLE U V (by rfl)).hom
  have hqp : q.asIdeal.comap φ = p.asIdeal := by
    change (PrimeSpectrum.comap φ q).asIdeal = p.asIdeal
    simpa [p, q, φ, V] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV (by rfl) hyV)
  have hφ : φ.IsIntegral := by
    simpa [φ, V, Scheme.Hom.appLE] using (g.isIntegral_app U hU)
  let : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  let : Algebra.IsIntegral Γ(X, U) Γ(Y, V) := by
    rwa [← algebraMap_isIntegral_iff]
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, V))) := by
    intro a b hab
    have : a.asIdeal.IsPrime := a.2
    change a.asIdeal.comap φ < b.asIdeal.comap φ
    exact Ideal.IsIntegral.under_lt_under (R := Γ(X, U)) (A := Γ(Y, V)) hab
  have hheight := Order.height_le_height_apply_of_strictMono
    (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, V))) hstrict q
  have hheight' : q.asIdeal.height ≤ p.asIdeal.height := by
    rw [← PrimeSpectrum.height_eq_orderHeight q,
      ← PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, V)) q)] at hheight
    simpa [p, φ, RingHom.algebraMap_toAlgebra, hqp] using hheight
  let := X.presheaf.algebra_section_stalk ⟨g y, hyU⟩
  let := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (g y)) p.asIdeal :=
    hU.isLocalization_stalk ⟨g y, hyU⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk y) q.asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Y.presheaf.stalk y),
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk (g y))]
  exact_mod_cast hheight'

private theorem normalizationScheme_isNormal
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    IsNormal (normalizationSchemeOverField k f) := by
  obtain ⟨I, Z, _, hZnorm, e, _⟩ :=
    exists_iso_normalizationSchemeOverField_coproduct_normal_irreducible k f
  exact isNormal_of_openCover ((sigmaOpenCover Z).pushforwardIso e.inv) hZnorm

private theorem normalizationStalk_isGeometricallyRegular
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x'))
    (x' : normalizationSchemeOverField k f)
    (hx : normalizationOverField k f x' = x) :
    let Xnorm := normalizationSchemeOverField k f
    let ν := normalizationOverField k f
    letI : Algebra k (Xnorm.presheaf.stalk x') :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
        StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
      (((ν ≫ f).stalkMap x').hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
    Algebra.IsGeometricallyRegular k (Xnorm.presheaf.stalk x') := by
  let Xnorm := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  let : IsFinite ν := isFinite_normalizationOverField k f
  have : IsIntegralHom ν := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType ν).mp
    (inferInstance : IsFinite ν) |>.1
  have : LocallyOfFiniteType (ν ≫ f) := inferInstance
  have : IsLocallyNoetherian Xnorm := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ f)
  let : IsNormal Xnorm := normalizationScheme_isNormal k f
  let B := Xnorm.presheaf.stalk x'
  let : IsDomain B := IsNormal.stalk_isDomain x'
  have hnormalB := IsNormal.stalk_normal x'
  have hdimB : ringKrullDim B ≤ 1 :=
    calc
      ringKrullDim B ≤ ringKrullDim (X.presheaf.stalk (ν x')) := by
        simpa [B, Xnorm] using ringKrullDim_stalk_le_of_isIntegralHom ν x'
      _ = 1 := by rw [hx, hdim]
  let : IsRegularLocalRing B :=
    isRegularLocalRing_of_normal_isDomain_dim_le_one B hnormalB hdimB
  let : Algebra k B :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
      StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
    (((ν ≫ f).stalkMap x').hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
  let : Algebra k (IsLocalRing.ResidueField B) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
  let hExplicit : Algebra k (IsLocalRing.ResidueField B) := inferInstance
  let hCanonical : Algebra k (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.algebra B
  have hAlgebra : hExplicit = hCanonical := by
    apply Algebra.algebra_ext
    intro a
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫
      Xnorm.Γevaluation x').hom) a =
      IsLocalRing.residue B (algebraMap k B a)
    let T := Spec (.of k)
    let : Algebra k (T.presheaf.stalk ((ν ≫ f).base x')) :=
      StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
    let : Algebra k (T.residueField ((ν ≫ f).base x')) :=
      IsLocalRing.ResidueField.algebra (T.presheaf.stalk ((ν ≫ f).base x'))
    have hbase :
        ((Scheme.ΓSpecIso (.of k)).inv ≫ T.Γevaluation ((ν ≫ f).base x')).hom =
          algebraMap k (T.residueField ((ν ≫ f).base x')) := by
      ext b
      rfl
    rw [← Scheme.Γevaluation_naturality (ν ≫ f) x']
    change (Scheme.Hom.residueFieldMap (ν ≫ f) x').hom
      ((((Scheme.ΓSpecIso (.of k)).inv ≫
        T.Γevaluation ((ν ≫ f).base x')).hom) a) = _
    rw [hbase]
    change (Scheme.Hom.residueFieldMap (ν ≫ f) x').hom
        (IsLocalRing.residue (T.presheaf.stalk ((ν ≫ f).base x'))
          (algebraMap k (T.presheaf.stalk ((ν ≫ f).base x')) a)) =
      IsLocalRing.residue B
        ((ν ≫ f).stalkMap x'
          (algebraMap k (T.presheaf.stalk ((ν ≫ f).base x')) a))
    exact congrArg (fun q => q.hom (algebraMap k
      (T.presheaf.stalk ((ν ≫ f).base x')) a))
      (Scheme.residue_residueFieldMap (ν ≫ f) x')
  have hsepB : @Algebra.IsSeparableExtension k (IsLocalRing.ResidueField B)
      _ _ hCanonical := by
    rw [← hAlgebra]
    exact hsep x' hx
  exact isGeometricallyRegular_of_isRegularLocalRing_residueField_isSeparable k B hsepB

private theorem algebra_isGeometricallyReduced_of_geometricallyReduced
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    (h : _root_.GeometricallyReduced.{u, u, u} k A) :
    Algebra.IsGeometricallyReduced k A :=
  (Algebra.isGeometricallyReduced_tfae k (ringExpChar k) A
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 5 6
      (by simp [_root_.GeometricallyReduced]) (by rfl) |>.mp h

private theorem geometricallyReduced_of_algebra_isGeometricallyReduced
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    (h : Algebra.IsGeometricallyReduced k A) :
    _root_.GeometricallyReduced.{u, u, u} k A :=
  (Algebra.isGeometricallyReduced_tfae k (ringExpChar k) A
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 6 5
      (by rfl) (by simp [_root_.GeometricallyReduced]) |>.mp h

/-- The `k`-algebra maps on stalks of a `k`-scheme are compatible with specialization maps. -/
private theorem stalkMap_algebraMap_eq_stalkSpecializes
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) {x z : X} (h : z ⤳ x)
    (a : k) :
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (g.base x)) :=
      StructureSheaf.stalkAlgebra k (g.base x)
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (g.base z)) :=
      StructureSheaf.stalkAlgebra k (g.base z)
    (g.stalkMap z).hom (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base z)) a) =
      (X.presheaf.stalkSpecializes h).hom
        ((g.stalkMap x).hom (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x)) a)) := by
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base x)) :=
    StructureSheaf.stalkAlgebra k (g.base x)
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base z)) :=
    StructureSheaf.stalkAlgebra k (g.base z)
  have hbase_a := congr_arg (fun q : CommRingCat.of k ⟶ _ ↦ q.hom a)
    (StructureSheaf.toStalk_stalkSpecializes (R := k) (h.map g.continuous))
  calc
    _ = (g.stalkMap z).hom
        (((Spec (.of k)).presheaf.stalkSpecializes (h.map g.continuous)).hom
          (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x)) a)) := by
            congr 1
            exact hbase_a.symm
    _ = _ := congr_arg (fun q :
        (Spec (.of k)).presheaf.stalk (g.base x) ⟶ X.presheaf.stalk z ↦ q.hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x)) a))
        (Scheme.Hom.stalkSpecializes_stalkMap g z x h)

private theorem normalizationGeneralizationStalk_isGeometricallyReduced
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x'))
    (x' z : normalizationSchemeOverField k f)
    (hx : normalizationOverField k f x' = x) (hz : z ⤳ x') :
    let Xnorm := normalizationSchemeOverField k f
    let ν := normalizationOverField k f
    letI : Algebra k (Xnorm.presheaf.stalk x') :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
        StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
      (((ν ≫ f).stalkMap x').hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
    letI : Algebra k (Xnorm.presheaf.stalk z) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base z)) :=
        StructureSheaf.stalkAlgebra k ((ν ≫ f).base z)
      (((ν ≫ f).stalkMap z).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base z)))).toAlgebra
    Algebra.IsGeometricallyReduced k (Xnorm.presheaf.stalk z) := by
  let Xnorm := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  let g := ν ≫ f
  let : IsFinite ν := isFinite_normalizationOverField k f
  have : LocallyOfFiniteType g := inferInstance
  have : IsLocallyNoetherian Xnorm := LocallyOfFiniteType.isLocallyNoetherian g
  let B := Xnorm.presheaf.stalk x'
  let : Algebra k B :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base x')) :=
      StructureSheaf.stalkAlgebra k (g.base x')
    (((g.stalkMap x').hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x')))).toAlgebra)
  have hregularB := normalizationStalk_isGeometricallyRegular k f x hdim hsep x' hx
  have hredB := Algebra.isGeometricallyReduced_of_isGeometricallyRegular k B
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Xnorm.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  have hzU : z ∈ U := hz.mem_open U.2 hxU
  let xU : U := ⟨x', hxU⟩
  let zU : U := ⟨z, hzU⟩
  let R := Γ(Xnorm, U)
  let p := hU.primeIdealOf xU
  let r := hU.primeIdealOf zU
  let e := Scheme.homeoOfIso hU.isoSpec
  let S := Xnorm.presheaf.stalk x'
  let T := Xnorm.presheaf.stalk z
  let : Algebra R S := Xnorm.presheaf.algebra_section_stalk xU
  let : Algebra R T := Xnorm.presheaf.algebra_section_stalk zU
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base x')) :=
    StructureSheaf.stalkAlgebra k (g.base x')
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base z)) :=
    StructureSheaf.stalkAlgebra k (g.base z)
  let : Algebra k S :=
    (((g.stalkMap x').hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x')))).toAlgebra)
  let : Algebra k T :=
    (((g.stalkMap z).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base z)))).toAlgebra)
  have hpr : r.asIdeal ≤ p.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    change e zU ⤳ e xU
    exact ((subtype_specializes_iff zU xU).mpr hz).map e.continuous
  let : IsLocalization.AtPrime S p.asIdeal := hU.isLocalization_stalk xU
  let : IsLocalization.AtPrime T r.asIdeal := hU.isLocalization_stalk zU
  have hprCompl : p.asIdeal.primeCompl ≤ r.asIdeal.primeCompl := fun a ha har => ha (hpr har)
  let : Algebra S T := IsLocalization.localizationAlgebraOfSubmonoidLe
    S T p.asIdeal.primeCompl r.asIdeal.primeCompl hprCompl
  let : IsScalarTower R S T := IsLocalization.localization_isScalarTower_of_submonoid_le
    S T p.asIdeal.primeCompl r.asIdeal.primeCompl hprCompl
  let M := Submonoid.map (algebraMap R S) r.asIdeal.primeCompl
  have hlocMap : IsLocalization M T := IsLocalization.isLocalization_of_submonoid_le
    S T p.asIdeal.primeCompl r.asIdeal.primeCompl hprCompl
  let : IsLocalization M T := hlocMap
  have hST : algebraMap S T = (Xnorm.presheaf.stalkSpecializes hz).hom := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact congr_arg CommRingCat.Hom.hom
      (TopCat.Presheaf.germ_stalkSpecializes Xnorm.presheaf hxU hz).symm
  let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' <| by
    rw [hST]
    ext a
    simp only [RingHom.coe_comp, RingHom.algebraMap_toAlgebra, Function.comp_apply]
    exact stalkMap_algebraMap_eq_stalkSpecializes k g hz _
  let hredAll : _root_.GeometricallyReduced.{u, u, u} k S :=
    geometricallyReduced_of_algebra_isGeometricallyReduced k S hredB
  have hTAll : _root_.GeometricallyReduced.{u, u, u} k T :=
    geometricallyReduced_localization k S M T hredAll
  exact algebra_isGeometricallyReduced_of_geometricallyReduced k T hTAll



private theorem isGeometricallyReducedAt_of_normalization_residueField_isSeparable_impl
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hred : _root_.IsReduced (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x')) :
    IsGeometricallyReducedAt f x := by
  rw [isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk]
  let : Algebra k (X.presheaf.stalk x) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
      StructureSheaf.stalkAlgebra k (f.base x)
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  let S := X.presheaf.stalk x
  let : _root_.IsReduced S := hred
  apply Algebra.IsGeometricallyReduced.of_forall_minimalPrimes
  intro q hq hqmin
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let R := Γ(X, U)
  let p : Ideal R := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime S p := hU.isLocalization_stalk ⟨x, hxU⟩
  let r : Ideal R := q.comap (algebraMap R S)
  have hrp : r.IsPrime := hq.comap _
  let yr : PrimeSpectrum R := ⟨r, hrp⟩
  let e : U ≃ₜ PrimeSpectrum R := Scheme.homeoOfIso hU.isoSpec
  let xU : U := e.symm yr
  have hprime_xU : (hU.primeIdealOf xU).asIdeal = r := by
    change (e xU).asIdeal = r
    simp [xU, yr]
  have hrle : r ≤ p := by
    have hd := (IsLocalization.isPrime_iff_isPrime_disjoint p.primeCompl S q).mp hq
    intro a ha
    by_contra hap
    exact (Set.disjoint_left.mp hd.2) hap ha
  have hxU_spec : (xU : X) ⤳ x := by
    have hrle : yr ≤ hU.primeIdealOf ⟨x, hxU⟩ := by
      change r ≤ p
      exact hrle
    have hs : yr ⤳ hU.primeIdealOf ⟨x, hxU⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hrle
    have hs' : xU ⤳ (⟨x, hxU⟩ : U) := by
      apply e.isInducing.specializes_iff.mp
      rw [show e xU = yr by simp [xU],
        show e ⟨x, hxU⟩ = hU.primeIdealOf ⟨x, hxU⟩ from rfl]
      exact hs
    exact (subtype_specializes_iff xU ⟨x, hxU⟩).mp hs'
  let Xnorm := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  let : IsFinite ν := isFinite_normalizationOverField k f
  let := Scheme.surjective_normalization X
    (finite_irreducibleComponents_of_locallyOfFiniteType k f)
  obtain ⟨y, hyη⟩ := ν.surjective (xU : X)
  let η := ν y
  have hηspec : η ⤳ x := by simpa [η, hyη] using hxU_spec
  let T := X.presheaf.stalk η
  let ηU : U := ⟨η, by simp [η, hyη]⟩
  let : Algebra R T := X.presheaf.algebra_section_stalk ηU
  have hprime_etaU : (hU.primeIdealOf ηU).asIdeal = r := by
    have heq : ηU = xU := Subtype.ext hyη
    rw [heq, hprime_xU]
  have : IsLocalization.AtPrime T r := by
    simpa only [hprime_etaU] using hU.isLocalization_stalk ηU
  have hprCompl : p.primeCompl ≤ r.primeCompl := fun a ha har ↦ ha (hrle har)
  let : Algebra S T := IsLocalization.localizationAlgebraOfSubmonoidLe
    S T p.primeCompl r.primeCompl hprCompl
  let : IsScalarTower R S T := IsLocalization.localization_isScalarTower_of_submonoid_le
    S T p.primeCompl r.primeCompl hprCompl
  have : IsLocalization (Submonoid.map (algebraMap R S) r.primeCompl) T :=
    IsLocalization.isLocalization_of_submonoid_le S T p.primeCompl r.primeCompl hprCompl
  have hximage : x ∈ ν '' closure ({y} : Set Xnorm) :=
    closure_minimal (Set.singleton_subset_iff.mpr
      (show η ∈ ν '' closure ({y} : Set Xnorm) from
        ⟨y, subset_closure (Set.mem_singleton y), by simp [η, hyη]⟩))
      ((Scheme.Hom.isClosedMap ν) _ isClosed_closure)
      (specializes_iff_mem_closure.mp hηspec)
  obtain ⟨x', hxcl, hxν⟩ := hximage
  have hyx' : y ⤳ x' := specializes_iff_mem_closure.mpr hxcl
  let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base y)) :=
    StructureSheaf.stalkAlgebra k ((ν ≫ f).base y)
  let : Algebra k (Xnorm.presheaf.stalk y) :=
    (((ν ≫ f).stalkMap y).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base y)))).toAlgebra
  have hbranch : Algebra.IsGeometricallyReduced k (Xnorm.presheaf.stalk y) :=
    normalizationGeneralizationStalk_isGeometricallyReduced
      k f x hdim hsep x' y hxν hyx'
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base η)) :=
    StructureSheaf.stalkAlgebra k (f.base η)
  let : Algebra k T :=
    ((f.stalkMap η).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base η)))).toAlgebra
  let : r.IsPrime := hrp
  have hmap_le : Submonoid.map (algebraMap R S) r.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ haq
    exact ha haq
  have hdenom : ∀ a : q.primeCompl,
      ∃ m : S, m * a.1 ∈ Submonoid.map (algebraMap R S) r.primeCompl := by
    rintro ⟨a, ha⟩
    obtain ⟨⟨b, c⟩, hab⟩ := IsLocalization.surj p.primeCompl a
    have hbq : algebraMap R S b ∉ q := by
      intro hbq
      have hamul : a * algebraMap R S (c : R) ∈ q := hab.symm ▸ hbq
      exact (hq.mem_or_mem hamul).elim ha fun hcq ↦
        hq.ne_top (q.eq_top_of_isUnit_mem hcq (IsLocalization.map_units S c))
    have hbr : b ∉ r := hbq
    refine ⟨algebraMap R S (c : R), ?_⟩
    refine ⟨b, hbr, ?_⟩
    simpa [mul_comm] using hab.symm
  have : IsLocalization.AtPrime T q := IsLocalization.isLocalization_of_is_exists_mul_mem T
    (Submonoid.map (algebraMap R S) r.primeCompl) q.primeCompl hmap_le hdenom
  have hfieldLoc : IsField (Localization.AtPrime q) :=
    minimal_prime_reduced_localization_isField S q hqmin
  let eField : T ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv
  let : Field T := ((MulEquiv.isField_congr eField.toMulEquiv).mpr hfieldLoc).toField
  have hscalar : algebraMap k (Xnorm.presheaf.stalk y) =
      ((ν.stalkMap y).hom.comp (algebraMap k T)) := by
    ext a
    change ((ν ≫ f).stalkMap y).hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base y)) a) =
      (ν.stalkMap y).hom ((f.stalkMap η).hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base η)) a))
    rw [congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp ν f y)]
    rfl
  let ψ : T →ₐ[k] Xnorm.presheaf.stalk y :=
    { toRingHom := (ν.stalkMap y).hom
      commutes' := fun a =>
        (congrArg (fun φ : k →+* Xnorm.presheaf.stalk y => φ a) hscalar).symm }
  have hgeoT : Algebra.IsGeometricallyReduced k T :=
    Algebra.IsGeometricallyReduced.of_injective ψ ψ.toRingHom.injective
  have hST : algebraMap S T = (X.presheaf.stalkSpecializes hηspec).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact congr_arg CommRingCat.Hom.hom
      (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hηspec).symm
  let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' <| by
    rw [hST]
    ext a
    simp only [RingHom.coe_comp, RingHom.algebraMap_toAlgebra, Function.comp_apply]
    exact stalkMap_algebraMap_eq_stalkSpecializes k f hηspec _
  let eST : T ≃ₐ[S] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)
  let eK : T ≃ₐ[k] Localization.AtPrime q := eST.restrictScalars k
  exact Algebra.IsGeometricallyReduced.of_injective
    (f := eK.symm.toAlgHom) eK.symm.injective

private theorem isGeometricallyRegularAt_normalization_of_residueField_isSeparable_impl
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x')) :
    let Xnorm := normalizationSchemeOverField k f
    let ν := normalizationOverField k f
    ∀ x' : Xnorm, ν x' = x → IsGeometricallyRegularAt (ν ≫ f) x' := by
  let Xnorm := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  change ∀ x' : Xnorm, ν x' = x → IsGeometricallyRegularAt (ν ≫ f) x'
  intro x' hx
  let : IsFinite ν := isFinite_normalizationOverField k f
  have : LocallyOfFiniteType (ν ≫ f) := inferInstance
  have : IsLocallyNoetherian Xnorm := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ f)
  let B := Xnorm.presheaf.stalk x'
  let : Algebra k B :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
      StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
    (((ν ≫ f).stalkMap x').hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
  exact (geometricallyRegularAt_tfae k Xnorm (ν ≫ f) x').out 1 3 |>.mpr
    (normalizationStalk_isGeometricallyRegular k f x hdim hsep x' hx)



/-- A reduced one-dimensional point is geometrically reduced if all residue fields above it in
the normalization are separable over the ground field. -/
@[stacks 0C3P "geometrically reduced at the original point"]
public theorem isGeometricallyReducedAt_of_normalization_residueField_isSeparable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hred : _root_.IsReduced (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x')) :
    IsGeometricallyReducedAt f x :=
  isGeometricallyReducedAt_of_normalization_residueField_isSeparable_impl k f x hred hdim hsep

/-- Every point of the normalization above a one-dimensional point is geometrically regular
when its residue field is separable over the ground field. -/
@[stacks 0C3P "geometrically regular on the normalization"]
public theorem isGeometricallyRegularAt_normalization_of_residueField_isSeparable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x')) :
    let Xnorm := normalizationSchemeOverField k f
    let ν := normalizationOverField k f
    ∀ x' : Xnorm, ν x' = x → IsGeometricallyRegularAt (ν ≫ f) x' :=
  isGeometricallyRegularAt_normalization_of_residueField_isSeparable_impl k f x hdim hsep

end AlgebraicGeometry

end

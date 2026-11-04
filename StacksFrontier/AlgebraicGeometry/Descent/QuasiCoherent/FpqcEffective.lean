module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineQuasicoherentEffective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcRefinementTransport
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effectivity of quasi-coherent descent data for an arbitrary fpqc covering family

The effectivity half of Stacks 023T says that for every fpqc covering family `{U i → S}` of a
scheme `S`, every quasi-coherent descent datum is effective. This file proves it over a spectrum
`Spec R` assuming the Zariski gluing `StandardSigmaEssSurj`, and over an arbitrary scheme assuming
either `StandardSigmaEssSurj` and the globalization `EffectiveOverSpecBaseGlobalizes`, or the
coproduct gluing `SigmaEssSurjOverAnyBase` and the one-element case
`EffectiveSigmaFamilyOverAnyBase`. It also proves the full faithfulness half of Stacks 023T at an
arbitrary index universe, and that every fpqc covering family is refined by one indexed in
`Type u`.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentData.StandardSigmaEssSurj`: restriction of
  quasi-coherent descent data along the coproduct refinement of a finite jointly surjective flat
  affine covering of `Spec R` is essentially surjective.
* `AlgebraicGeometry.QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes`: effectivity over
  the bases `Spec R` implies effectivity over an arbitrary base.
* `AlgebraicGeometry.QuasicoherentDescentData.SigmaEssSurjOverAnyBase`: the coproduct refinement
  of a `Type u`-indexed family over an arbitrary base is essentially surjective.
* `AlgebraicGeometry.QuasicoherentDescentData.EffectiveSigmaFamilyOverAnyBase`: every
  quasi-coherent descent datum for the single morphism `∐ X i ⟶ S` attached to a `Type u`-indexed
  fpqc covering family is effective.
* `AlgebraicGeometry.QuasicoherentDescentData.affineZeroHypercover`: an affine open covering of a
  scheme, as a `0`-hypercover for the fpqc precoverage.

## Main results

* `Stacks.Descent.isEffective_of_faithfullyFlat'`: for a faithfully flat `φ : R ⟶ S` of
  commutative rings, every quasi-coherent descent datum for the one-element family `Spec φ` is
  effective.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_sigmaFamily_of_affine_flat`: descent
  data for the coproduct of a standard fpqc covering of `Spec R` are effective.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_of_standardFpqc`: assuming
  `StandardSigmaEssSurj`, descent data for a standard fpqc covering of `Spec R` are effective
  (the effectivity half of Stacks 023S).
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_of_mem_fpqcPrecoverage_spec`: assuming
  `StandardSigmaEssSurj`, descent data for an arbitrary fpqc covering family of `Spec R` are
  effective.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_of_mem_fpqcPrecoverage` and
  `AlgebraicGeometry.QuasicoherentDescentData.isEffective_of_mem_fpqcPrecoverage_of_sigma`: the
  effectivity half of Stacks 023T for an arbitrary fpqc covering family of an arbitrary scheme,
  under the two pairs of hypotheses above.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveOverSpecBaseGlobalizes_of_forall` and
  `AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase_of_forall`: the
  effectivity half of Stacks 023T implies `EffectiveOverSpecBaseGlobalizes`, respectively
  `EffectiveSigmaFamilyOverAnyBase`.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveOverSpecBaseGlobalizes_of_sigma`:
  `SigmaEssSurjOverAnyBase` and `EffectiveSigmaFamilyOverAnyBase` imply
  `EffectiveOverSpecBaseGlobalizes`.
* `…nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`:
  the full faithfulness half of Stacks 023T at an arbitrary index universe.
* `AlgebraicGeometry.QuasicoherentDescentData.exists_small_fpqc_refinement`: every fpqc covering
  family of a scheme is refined by one indexed in `Type u`.

## Implementation notes

`AlgebraicGeometry.QuasicoherentDescentData.isEffective_sigmaFamily_of_affine_flat` needs the base
to be literally `Spec R`, not merely affine: moving the base of a one-element family to an
isomorphic scheme would need `canonicalDescentFunctorCompPullFunctorIso` along an isomorphism,
and it is available only over `𝟙 S`.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe v w t u

namespace Stacks.Descent

/-- For a faithfully flat morphism `φ : R ⟶ S` of commutative rings, every quasi-coherent descent
datum for the one-element family `Spec φ` is effective. -/
public theorem isEffective_of_faithfullyFlat' {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FaithfullyFlat) {ι : Type t} [Unique ι]
    (D : AlgebraicGeometry.QuasicoherentDescentData (fun _ : ι ↦ AlgebraicGeometry.Spec.map φ)) :
    D.IsEffective := by
  let _i : Algebra R S := φ.hom.toAlgebra
  have hofHom : CommRingCat.ofHom (algebraMap R S) = φ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  exact isEffective_of_faithfullyFlat_affine φ
    (hofHom ▸ (CommRingCat.isPushout_tensorProduct R S S).flip) D hφ MilnorPatching.tensorPushout

end Stacks.Descent

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-- For every finite jointly surjective family of flat morphisms from affine schemes to a
spectrum `Spec R`, restriction of quasi-coherent descent data along the coproduct refinement
`AlgebraicGeometry.QuasicoherentDescentData.toSigmaFamily` is essentially surjective: every
quasi-coherent descent datum for the family is isomorphic to the restriction of one for the
one-element family `{∐ X i → Spec R}`. -/
public abbrev StandardSigmaEssSurj : Prop :=
  ∀ {R : CommRingCat.{u}} (𝒱 : PreZeroHypercover.{0} (Spec R)), Finite 𝒱.I₀ →
    (∀ i, IsAffine (𝒱.X i)) → (∀ i, Flat (𝒱.f i)) → (⋃ i, Set.range (𝒱.f i) = Set.univ) →
      (pullFunctor (toSigmaFamily 𝒱)).EssSurj

/-- Every quasi-coherent descent datum for the one-element family given by the coproduct of a
standard fpqc covering of `Spec R` is effective. -/
public theorem isEffective_sigmaFamily_of_affine_flat {R : CommRingCat.{u}}
    (𝒱 : PreZeroHypercover.{w} (Spec R)) [Finite 𝒱.I₀] [Small.{u} 𝒱.I₀]
    [∀ i, IsAffine (𝒱.X i)] [∀ i, Flat (𝒱.f i)]
    (hsurj : ⋃ i, Set.range (𝒱.f i) = Set.univ)
    (D : QuasicoherentDescentData (sigmaFamily 𝒱).f) : D.IsEffective := by
  have hsu₀ : Surjective (Sigma.desc 𝒱.f) := Surjective.sigmaDesc_of_union_range_eq_univ hsurj
  set e := (∐ 𝒱.X).isoSpec with he
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = e.inv ≫ Sigma.desc 𝒱.f := ⟨_, Spec.map_preimage _⟩
  obtain ⟨hfl, hsu⟩ : Flat (Spec.map φ) ∧ Surjective (Spec.map φ) := by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩
  refine isEffective_of_forall_isEffective_of_mem_fpqcPrecoverage
    (toSingletonFamily (PreZeroHypercover.singleton.{0} (Spec.map φ))
      (Sigma.desc 𝒱.f) (fun _ ↦ e.inv) (fun _ ↦ hφ.symm)) ?_
    (fun D ↦ Stacks.Descent.isEffective_of_faithfullyFlat' _
      ((flat_and_surjective_SpecMap_iff _).mp ⟨hfl, hsu⟩) D) D
  rw [PreZeroHypercover.presieve₀_singleton]
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-- The effectivity half of Stacks 023S over `Spec R`, assuming `StandardSigmaEssSurj`: every
quasi-coherent descent datum for a standard fpqc covering of a spectrum (a finite jointly
surjective family of flat morphisms from affine schemes, Stacks 022F) is effective. -/
public theorem isEffective_of_standardFpqc (hess : StandardSigmaEssSurj.{u})
    {R : CommRingCat.{u}} (𝒱 : PreZeroHypercover.{0} (Spec R)) [Finite 𝒱.I₀]
    [∀ i, IsAffine (𝒱.X i)] [∀ i, Flat (𝒱.f i)]
    (hsurj : ⋃ i, Set.range (𝒱.f i) = Set.univ)
    (D : QuasicoherentDescentData 𝒱.f) : D.IsEffective :=
  have := hess 𝒱 ‹_› (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hsurj
  isEffective_of_essSurj_pullFunctor_toSigmaFamily 𝒱
    (fun D₀ ↦ isEffective_sigmaFamily_of_affine_flat 𝒱 hsurj D₀) D

/-- The effectivity half of Stacks 023T over a spectrum, assuming `StandardSigmaEssSurj`: every
quasi-coherent descent datum for an arbitrary fpqc covering family of `Spec R` is effective. -/
public theorem isEffective_of_mem_fpqcPrecoverage_spec (hess : StandardSigmaEssSurj.{u})
    {R : CommRingCat.{u}} (𝒰 : PreZeroHypercover.{v} (Spec R))
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage (Spec R))
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective := by
  obtain ⟨V, Φ, hfin, hV, -⟩ := exists_finite_affineCover_flat_refinement 𝒰 h𝒰
  have _hfin : Finite V.cover.toPreZeroHypercover.I₀ := hfin
  have _haff : ∀ i, IsAffine (V.cover.toPreZeroHypercover.X i) := fun i ↦
    inferInstanceAs (IsAffine (Spec (V.X i)))
  have _hflat : ∀ i, Flat (V.cover.toPreZeroHypercover.f i) := fun i ↦ V.map_prop i
  refine isEffective_of_forall_isEffective_of_hom Φ hV (fun D' ↦ ?_) D
  refine isEffective_of_standardFpqc hess V.cover.toPreZeroHypercover ?_ D'
  exact Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_iUnion.mpr ⟨V.idx x, V.covers x⟩

/-- If every quasi-coherent descent datum for every fpqc covering family of every spectrum
`Spec R` is effective, then the same holds over an arbitrary base scheme. -/
public abbrev EffectiveOverSpecBaseGlobalizes : Prop :=
  (∀ {R : CommRingCat.{u}} (𝒱 : PreZeroHypercover.{v} (Spec R)),
      𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage (Spec R) →
        ∀ D : QuasicoherentDescentData 𝒱.f, D.IsEffective) →
    ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S → ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective

/-- The effectivity half of Stacks 023T for an arbitrary fpqc covering family of an arbitrary
scheme, assuming `StandardSigmaEssSurj` and `EffectiveOverSpecBaseGlobalizes`. -/
public theorem isEffective_of_mem_fpqcPrecoverage (hess : StandardSigmaEssSurj.{u})
    (hglob : EffectiveOverSpecBaseGlobalizes.{v, u}) {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  hglob (fun 𝒱 h𝒱 D' ↦ isEffective_of_mem_fpqcPrecoverage_spec hess 𝒱 h𝒱 D') 𝒰 h𝒰 D

/-- The effectivity half of Stacks 023T over every scheme implies
`EffectiveOverSpecBaseGlobalizes`. -/
public theorem effectiveOverSpecBaseGlobalizes_of_forall
    (h : ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S → ∀ D : QuasicoherentDescentData 𝒰.f,
        D.IsEffective) :
    EffectiveOverSpecBaseGlobalizes.{v, u} :=
  fun _ _ 𝒰 h𝒰 D ↦ h 𝒰 h𝒰 D

/-! ### Full faithfulness at an arbitrary index universe -/

/-- The full faithfulness half of Stacks 023T at an arbitrary index universe: for every fpqc
covering family of every scheme, the canonical descent functor on quasi-coherent modules is fully
faithful. -/
@[ega "IV 4.8.3" "more general", sga "1 VIII 1.2" "more general"]
public theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage
    {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor 𝒰.f).FullyFaithful :=
  have hpull := nonempty_fullyFaithful_pullFunctor_of_mem_fpqcPrecoverage
    (toTrivialFamily 𝒰) h𝒰
  have : ∀ i, IsOpenImmersion ((PreZeroHypercover.singleton.{0} (𝟙 S)).f i) := fun _ ↦
    inferInstanceAs (IsOpenImmersion (𝟙 S))
  have hsing : Nonempty
      (canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f).FullyFaithful :=
    Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski
      (f := (PreZeroHypercover.singleton.{0} (𝟙 S)).f)
      (by simpa [PreZeroHypercover.singleton] using Scheme.Hom.opensRange_of_isIso (𝟙 S))
  ⟨(hsing.some.comp hpull.some).ofIso
    (canonicalDescentFunctorCompPullFunctorIso (toTrivialFamily 𝒰))⟩

/-! ### A small refinement of an arbitrary fpqc covering -/

/-- A factorization through the first projection of a fibre product turns into one through the
second: if `a ≫ p₁ = b` then `(a ≫ p₂) ≫ g = b ≫ f`. -/
public theorem comp_pullbackSnd_comp {A X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] (a : A ⟶ pullback f g) (b : A ⟶ X) (h : a ≫ pullback.fst f g = b) :
    (a ≫ pullback.snd f g) ≫ g = b ≫ f := by
  rw [← h, Category.assoc, Category.assoc, pullback.condition]

/-- The affine open covering `AlgebraicGeometry.Scheme.affineCover` of a scheme, as a
`0`-hypercover for the fpqc precoverage. -/
public noncomputable def affineZeroHypercover (S : Scheme.{u}) :
    Scheme.fpqcPrecoverage.ZeroHypercover.{u} S where
  __ := S.affineCover.toPreZeroHypercover
  mem₀ := by
    change _ ∈ Scheme.qcPrecoverage S ∧ _ ∈ Scheme.precoverage (@Flat.{u}) S
    exact ⟨Scheme.zariskiPrecoverage_le_qcPrecoverage _ S.affineCover.mem₀,
      (Scheme.presieve₀_mem_precoverage_iff _).mpr
        ⟨fun x ↦ ⟨_, S.affineCover.covers x⟩, fun i ↦ inferInstance⟩⟩

/-- Every fpqc covering family of a scheme is refined by an fpqc covering family indexed in
`Type u`. -/
public theorem exists_small_fpqc_refinement {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) :
    ∃ (𝒲 : PreZeroHypercover.{u} S) (_ : 𝒲.Hom 𝒰),
      𝒲.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S := by
  classical
  set 𝒜 := affineZeroHypercover S with h𝒜
  have hbase (a : 𝒜.I₀) : (𝒰.pullback₁ (𝒜.f a)).presieve₀ ∈
      Scheme.fpqcPrecoverage.{u} (𝒜.X a) :=
    ((⟨𝒰, h𝒰⟩ : Scheme.fpqcPrecoverage.ZeroHypercover S).pullback₁ (𝒜.f a)).mem₀
  have (a : 𝒜.I₀) : IsAffine (𝒜.X a) := Scheme.isAffine_affineCover S a
  choose W ref hfin hfpqc hopen using fun a : 𝒜.I₀ ↦
    exists_finite_affineCover_flat_refinement (𝒰.pullback₁ (𝒜.f a)) (hbase a)
  refine ⟨(𝒜.bind (fun a ↦ ⟨(W a).cover.toPreZeroHypercover, hfpqc a⟩)).toPreZeroHypercover,
    { s₀ p := (ref p.1).s₀ p.2
      h₀ p := (ref p.1).h₀ p.2 ≫ pullback.snd _ _
      w₀ p := comp_pullbackSnd_comp _ _ _ _ ((ref p.1).w₀ p.2) },
    (𝒜.bind (fun a ↦ ⟨(W a).cover.toPreZeroHypercover, hfpqc a⟩)).mem₀⟩

/-! ### Reduction of the globalization to the one-element case -/

/-- For every `Type u`-indexed family `{X i ⟶ S}` over an arbitrary scheme, every quasi-coherent
descent datum for the family is isomorphic to the restriction of one for the one-element family
`{∐ X i ⟶ S}`. -/
public abbrev SigmaEssSurjOverAnyBase : Prop :=
  ∀ {S : Scheme.{u}} (𝒲 : PreZeroHypercover.{u} S), (pullFunctor (toSigmaFamily 𝒲)).EssSurj

/-- For every `Type u`-indexed fpqc covering family `{X i ⟶ S}` of an arbitrary scheme `S`, every
quasi-coherent descent datum for the single morphism `∐ X i ⟶ S` is effective. -/
public abbrev EffectiveSigmaFamilyOverAnyBase : Prop :=
  ∀ {S : Scheme.{u}} (𝒲 : PreZeroHypercover.{u} S),
    𝒲.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
      ∀ D : QuasicoherentDescentData (sigmaFamily 𝒲).f, D.IsEffective

/-- The effectivity half of Stacks 023T, assuming `SigmaEssSurjOverAnyBase` and
`EffectiveSigmaFamilyOverAnyBase`: for every fpqc covering family of every scheme, at every index
universe, every quasi-coherent descent datum is effective. -/
public theorem isEffective_of_mem_fpqcPrecoverage_of_sigma
    (hess : SigmaEssSurjOverAnyBase.{u}) (hsig : EffectiveSigmaFamilyOverAnyBase.{u})
    {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective := by
  obtain ⟨𝒲, Φ, h𝒲⟩ := exists_small_fpqc_refinement 𝒰 h𝒰
  refine isEffective_of_forall_isEffective_of_hom Φ h𝒲 (fun D' ↦ ?_) D
  have := hess 𝒲
  exact isEffective_of_essSurj_pullFunctor_toSigmaFamily 𝒲 (hsig 𝒲 h𝒲) D'

/-- `SigmaEssSurjOverAnyBase` and `EffectiveSigmaFamilyOverAnyBase` imply
`EffectiveOverSpecBaseGlobalizes`. -/
public theorem effectiveOverSpecBaseGlobalizes_of_sigma
    (hess : SigmaEssSurjOverAnyBase.{u}) (hsig : EffectiveSigmaFamilyOverAnyBase.{u}) :
    EffectiveOverSpecBaseGlobalizes.{v, u} :=
  fun _ _ 𝒰 h𝒰 D ↦ isEffective_of_mem_fpqcPrecoverage_of_sigma hess hsig 𝒰 h𝒰 D

/-- The effectivity half of Stacks 023T for `Type u`-indexed families implies
`EffectiveSigmaFamilyOverAnyBase`. -/
public theorem effectiveSigmaFamilyOverAnyBase_of_forall
    (h : ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S),
      𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
        ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective) :
    EffectiveSigmaFamilyOverAnyBase.{u} :=
  fun 𝒲 h𝒲 D ↦ isEffective_of_forall_isEffective_of_mem_fpqcPrecoverage
    (toSigmaFamily 𝒲) h𝒲 (fun D' ↦ h 𝒲 h𝒲 D') D

end QuasicoherentDescentData

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.Topology.ExtremallyDisconnected
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.ExtremallyDisconnected.Defs
public import StacksCore.Topology.Proper.Bijection
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreEtale.FiberwiseIncomparable.ProfiniteSpectra
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
public import StacksFrontier.Topology.ExtremallyDisconnected.Characterization
public import StacksFrontier.Topology.Spectral.ProfiniteCharacterization

/-!
# Extremal disconnectedness under quasi-finite finitely presented ring maps

Let `A → B` be a quasi-finite, finitely presented homomorphism of commutative rings. If every
residue field of `A` is separably closed and the prime spectrum of `A` is Hausdorff and
extremally disconnected, then the prime spectrum of `B` is extremally disconnected.

## Main results

* `AlgebraicGeometry.ProEtale.extremallyDisconnected_primeSpectrum_of_quasiFinite`: a
  quasi-finite, finitely presented algebra over a ring with separably closed residue fields and
  Hausdorff extremally disconnected spectrum has extremally disconnected prime spectrum.

## Implementation notes

The ring map is represented by an algebra structure, its quasi-finiteness and finite presentation
by Mathlib's `Algebra.QuasiFinite` and `Algebra.FinitePresentation`, and the condition on the
residue fields is indexed by `PrimeSpectrum A`. The two rings may live in different universes;
the geometric input is stated for schemes over a single universe, so the proof first transports
both rings to their common universe along `ULift.ringEquiv`.

The decomposition of `Spec B → Spec A` into strata with finite locally free covers splitting the
reduced pullback comes from
`AlgebraicGeometry.exists_finite_affine_stratification_split_reduction`. Separable closedness of
the residue fields makes the splitting a bijection on points: the residue tensor product of a
pullback triplet has a one-point spectrum, so the underlying space of the pullback is the
set-theoretic fibre product. A continuous section of each cover then exhibits the preimage of a
stratum as a finite disjoint union of copies of that stratum.

## References

* [Stacks Project, Tag 0985](https://stacks.math.columbia.edu/tag/0985)
-/

@[expose] public noncomputable section

open scoped TensorProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ProEtale

private lemma isClopen_of_isConstructible_of_compact_t2
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Set X) (hs : Topology.IsConstructible s) : IsClopen s := by
  classical
  unfold Topology.IsConstructible at hs
  induction hs using BooleanSubalgebra.closure_bot_sup_induction with
  | mem U hU =>
      have hcompact : IsCompact U := by
        simpa using hU.2 isCompact_univ isOpen_univ
      exact ⟨hcompact.isClosed, hU.1⟩
  | bot => exact ⟨isClosed_empty, isOpen_empty⟩
  | sup U _ V _ hU hV => simpa using hU.union hV
  | compl U _ hU => exact hU.compl

private lemma extremallyDisconnected_subtype_of_isOpen
    {X : Type*} [TopologicalSpace X] [ExtremallyDisconnected X]
    (s : Set X) (hs : IsOpen s) : ExtremallyDisconnected s := by
  refine ⟨fun U hU ↦ ?_⟩
  have hU' : IsOpen ((Subtype.val : s → X) '' U) :=
    hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp hU
  have hcl : IsOpen (closure ((Subtype.val : s → X) '' U)) :=
    ExtremallyDisconnected.open_closure _ hU'
  have heq : closure U = (Subtype.val : s → X) ⁻¹' closure ((Subtype.val : s → X) '' U) := by
    ext x; exact closure_subtype
  rw [heq]
  exact hcl.preimage continuous_subtype_val

private lemma extremallyDisconnected_of_finite_clopen_cover
    {X : Type*} [TopologicalSpace X] {n : ℕ} (s : Fin n → Set X)
    (hopen : ∀ i, IsOpen (s i)) (hclosed : ∀ i, IsClosed (s i))
    (hcover : (⋃ i, s i) = Set.univ)
    (hed : ∀ i, ExtremallyDisconnected (s i)) : ExtremallyDisconnected X := by
  refine ⟨fun U hU ↦ ?_⟩
  have hpart : U = ⋃ i, U ∩ s i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hcover]; simp : x ∈ ⋃ i, s i)
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩; exact hx
  have hclosureopen : ∀ i, IsOpen (closure (U ∩ s i)) := by
    intro i
    have hUi : IsOpen ((Subtype.val : s i → X) ⁻¹' U) := hU.preimage continuous_subtype_val
    have hrel := hed i |>.open_closure ((Subtype.val : s i → X) ⁻¹' U) hUi
    have himage : ((Subtype.val : s i → X) ''
        closure ((Subtype.val : s i → X) ⁻¹' U)) = closure (U ∩ s i) := by
      calc
        _ = closure ((Subtype.val : s i → X) ''
            ((Subtype.val : s i → X) ⁻¹' U)) :=
              (hclosed i).isClosedEmbedding_subtypeVal.closure_image_eq _ |>.symm
        _ = closure (U ∩ s i) := by congr 1; ext x; simp [and_comm]
    rw [← himage]
    exact (hopen i).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp hrel
  rw [hpart, closure_iUnion_of_finite]
  exact isOpen_iUnion hclosureopen

private lemma isSepClosed_of_ringEquiv {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (hK : IsSepClosed K) : IsSepClosed L := by
  refine ⟨fun p hp ↦ ?_⟩
  have hs : (p.map e.symm.toRingHom).Splits :=
    hK.splits_of_separable _ (Polynomial.Separable.map hp)
  simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
    RingEquiv.comp_symm, RingHom.id_apply, Polynomial.map_id] using hs.map e.toRingHom

private lemma ulift_residueField_isSepClosed
    (A : Type u) [CommRing A]
    (hres : ∀ p : PrimeSpectrum A, IsSepClosed p.asIdeal.ResidueField)
    (p' : PrimeSpectrum (ULift.{max u v} A)) :
    IsSepClosed p'.asIdeal.ResidueField := by
  let e : ULift.{max u v} A ≃+* A := ULift.ringEquiv
  let p : PrimeSpectrum A := PrimeSpectrum.comap e.symm.toRingHom p'
  have hpoint : PrimeSpectrum.comap e.toRingHom p = p' :=
    (PrimeSpectrum.comapEquiv e).symm_apply_apply p'
  have hp : p'.asIdeal = p.asIdeal.comap e.toRingHom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hpoint).symm
  let eκ := Ideal.residueFieldRingEquiv (J := p'.asIdeal) (K := p.asIdeal) e hp
  exact isSepClosed_of_ringEquiv eκ.symm (hres p)

@[ega "IV 4.3.3" "special case"]
private lemma primeSpectrum_tensorProduct_subsingleton_of_isSepClosed
    {k : Type*} {L K : Type*} [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [IsSepClosed k] [Module.Finite k K] :
    Subsingleton (PrimeSpectrum (L ⊗[k] K)) := by
  let : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let : IsPurelyInseparable k K := inferInstance
  let e := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K L
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-- The prime spectrum is a subsingleton if it is one for a ring isomorphic to it. -/
private lemma subsingleton_primeSpectrum_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : Subsingleton (PrimeSpectrum R)) : Subsingleton (PrimeSpectrum S) :=
  ⟨fun _ _ ↦ (PrimeSpectrum.homeomorphOfRingEquiv e).symm.injective (h.elim _ _)⟩

private lemma pullbackTriplet_tensor_subsingleton
    {Y X Z : Scheme} (f : Y ⟶ Z) (g : X ⟶ Z)
    (T : Scheme.Pullback.Triplet f g)
    [Algebra (Z.residueField T.s) (Y.residueField T.x)]
    [Algebra (Z.residueField T.s) (X.residueField T.y)]
    [Module.Finite (Z.residueField T.s) (Y.residueField T.x)]
    (hsep : IsSepClosed (Z.residueField T.s))
    (hL : algebraMap (Z.residueField T.s) (Y.residueField T.x) =
      ((Z.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom)
    (hK : algebraMap (Z.residueField T.s) (X.residueField T.y) =
      ((Z.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom) :
    Subsingleton (Spec T.tensor) := by
  let k := Z.residueField T.s
  let L := Y.residueField T.x
  let K := X.residueField T.y
  have hTensor : Subsingleton (PrimeSpectrum (L ⊗[k] K)) :=
    subsingleton_primeSpectrum_of_ringEquiv (Algebra.TensorProduct.comm k K L).toRingEquiv
      (primeSpectrum_tensorProduct_subsingleton_of_isSepClosed (k := k) (L := K) (K := L))
  let f₀ : k ⟶ L := (Z.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x
  let g₀ : k ⟶ K := (Z.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y
  have hf₀ : f₀ = CommRingCat.ofHom (algebraMap k L) := by
    ext x; exact (congrArg (fun q : _ →+* _ => q x) hL).symm
  have hg₀ : g₀ = CommRingCat.ofHom (algebraMap k K) := by
    ext x; exact (congrArg (fun q : _ →+* _ => q x) hK).symm
  have hpush : IsPushout f₀ g₀
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := L) (B := K)))
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := K)).toRingHom) := by
    rw [hf₀, hg₀]
    exact CommRingCat.isPushout_tensorProduct k L K
  let h₀ := (IsPushout.of_hasPushout f₀ g₀).isColimit
  let e : CommRingCat.of (L ⊗[k] K) ≅ T.tensor := by
    show CommRingCat.of (L ⊗[k] K) ≅ pushout f₀ g₀
    exact h₀.coconePointUniqueUpToIso hpush.isColimit |>.symm
  exact subsingleton_primeSpectrum_of_ringEquiv e.commRingCatIsoToRingEquiv hTensor

private lemma ulift_quasiFinite_and_finitePresentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] [Algebra.FinitePresentation A B] :
    @Algebra.QuasiFinite (ULift.{max u v} A) (ULift.{max u v} B) _ _
        (ULift.algebra' A (ULift.{max u v} B)) ∧
      @Algebra.FinitePresentation (ULift.{max u v} A) (ULift.{max u v} B) _ _
        (ULift.algebra' A (ULift.{max u v} B)) := by
  let A' := ULift.{max u v} A
  let B' := ULift.{max u v} B
  let : Algebra A' B' := ULift.algebra' A B'
  let eA : A' ≃+* A := ULift.ringEquiv
  let eB : B' ≃+* B := ULift.ringEquiv
  let f' : A' →+* B' := eB.symm.toRingHom.comp
    ((algebraMap A B).comp eA.toRingHom)
  have hmap : f' = algebraMap A' B' := by ext x; rfl
  have hqf : RingHom.QuasiFinite (algebraMap A B) :=
    RingHom.quasiFinite_algebraMap.mpr inferInstance
  have hAqf : RingHom.QuasiFinite eA.toRingHom :=
    .of_finite (.of_surjective _ eA.surjective)
  have hBqf : RingHom.QuasiFinite eB.symm.toRingHom :=
    .of_finite (.of_surjective _ eB.symm.surjective)
  have hqf' : RingHom.QuasiFinite f' := hBqf.comp (hqf.comp hAqf)
  have hfp : RingHom.FinitePresentation (algebraMap A B) :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hAfp : RingHom.FinitePresentation eA.toRingHom :=
    RingHom.FinitePresentation.of_bijective eA.bijective
  have hBfp : RingHom.FinitePresentation eB.symm.toRingHom :=
    RingHom.FinitePresentation.of_bijective eB.symm.bijective
  have hfp' : RingHom.FinitePresentation f' := hBfp.comp (hfp.comp hAfp)
  refine ⟨?_, ?_⟩
  · show Algebra.QuasiFinite A' B'
    rw [← RingHom.quasiFinite_algebraMap, ← hmap]
    exact hqf'
  · show Algebra.FinitePresentation A' B'
    rw [← RingHom.finitePresentation_algebraMap, ← hmap]
    exact hfp'

private lemma specMap_has_quasiFinite_finitePresentation
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] [Algebra.FinitePresentation A B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
    LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
    AlgebraicGeometry.FinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  let φ : A →+* B := algebraMap A B
  have hfp : RingHom.FinitePresentation φ := RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hft : RingHom.FiniteType φ := RingHom.FiniteType.of_finitePresentation hfp
  have hlfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact hfp
  have hft' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact hft
  have hqf' : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  let : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) := hlfp
  exact ⟨hft', hqf', ⟨hlfp, inferInstance, inferInstance⟩⟩

private lemma profinite_primeSpectrum_of_quasiFinite_of_t2
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] (hT2 : T2Space (PrimeSpectrum A)) :
    IsProfiniteStacks (PrimeSpectrum B) := by
  have hprofA : IsProfiniteStacks (PrimeSpectrum A) :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mpr
      ⟨inferInstance, hT2,
        (spectralSpace_profinite_of_t2 (X := PrimeSpectrum A)).2⟩
  exact isProfiniteStacks_primeSpectrum_of_quasiFinite A B hprofA

private def schemeIsoHomeomorph {X Y : Scheme} (e : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)

private lemma t2Space_of_affine_quasiFinite
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X] (f : Y ⟶ X)
    [LocallyQuasiFinite f] [T2Space X] : T2Space Y := by
  let A := Γ(X, ⊤)
  let B := Γ(Y, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.QuasiFinite A B :=
    (HasRingHomProperty.appTop (P := @LocallyQuasiFinite) f inferInstance)
  have hA : T2Space (PrimeSpectrum A) := (schemeIsoHomeomorph X.isoSpec).t2Space
  have hB : T2Space (PrimeSpectrum B) :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mp
      (profinite_primeSpectrum_of_quasiFinite_of_t2 A B hA)).2.1
  have : T2Space (Spec Γ(Y, ⊤)) := hB
  exact (schemeIsoHomeomorph Y.isoSpec).symm.t2Space

private lemma residueFieldMap_quasiFinite_of_t1
    {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [T1Space Y] (y : Y) :
    (f.residueFieldMap y).hom.QuasiFinite := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp isClosed_singleton
  have : LocallyQuasiFinite
      (Spec.map (f.residueFieldMap y) ≫ X.fromSpecResidueField (f y)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have : LocallyQuasiFinite (Spec.map (f.residueFieldMap y)) :=
    LocallyQuasiFinite.of_comp _ (X.fromSpecResidueField (f y))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this

private lemma pullbackTriplet_subsingleton_of_quasiFinite
    {Y X Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Z)
    [LocallyQuasiFinite f] [T1Space Y]
    (hres : ∀ z : Z, IsSepClosed (Z.residueField z))
    (T : Scheme.Pullback.Triplet f g) : Subsingleton (Spec T.tensor) := by
  let a := (Z.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x
  let b := (Z.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y
  let : Algebra (Z.residueField T.s) (Y.residueField T.x) := a.hom.toAlgebra
  let : Algebra (Z.residueField T.s) (X.residueField T.y) := b.hom.toAlgebra
  have hq : a.hom.QuasiFinite :=
    (residueFieldMap_quasiFinite_of_t1 f T.x).comp
      (RingHom.QuasiFinite.of_finite
        (RingHom.Finite.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr T.hx).inv).2))
  have : Algebra.QuasiFinite (Z.residueField T.s) (Y.residueField T.x) := hq
  have : Module.Finite (Z.residueField T.s) (Y.residueField T.x) :=
    Module.Finite.of_quasiFinite
  exact pullbackTriplet_tensor_subsingleton f g T (hres T.s) rfl rfl

private def schemeSigmaHomeomorph {ι : Type} (f : ι → Scheme.{u})
    [Small.{u} ι] : (Σ i, f i) ≃ₜ (↑(∐ f)) :=
  TopCat.homeoOfIso
    ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
      (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

private lemma schemeSigmaHomeomorph_mk {ι : Type} (f : ι → Scheme.{u})
    [Small.{u} ι] (i : ι) (x : f i) :
    schemeSigmaHomeomorph f ⟨i, x⟩ = (Sigma.ι f i).base x := by
  let F := Scheme.forgetToTop
  let c := TopCat.sigmaCofanIsColimit (fun j ↦ (f j).toTopCat)
  have h := colimit.isoColimitCocone_ι_inv_assoc ⟨_, c⟩ (Discrete.mk i)
    (sigmaComparison F f)
  have h' : (TopCat.sigmaCofan (fun j ↦ (f j).toTopCat)).inj i ≫
      (colimit.isoColimitCocone ⟨_, c⟩).inv ≫ sigmaComparison F f =
      F.map (Sigma.ι f i) := by
    exact h.trans (ι_comp_sigmaComparison F f i)
  exact congrArg (fun k : (f i).toTopCat ⟶ F.obj (∐ f) ↦ k x) h'

/-- The inclusion of the reduced subscheme is surjective on points. -/
private lemma nilradical_subschemeι_surjective (X : Scheme) :
    Function.Surjective X.nilradical.subschemeι := fun x ↦ by
  have hx : x ∈ Set.range X.nilradical.subschemeι := by
    rw [X.nilradical.range_subschemeι, X.support_nilradical]
    simp
  exact Set.mem_range.mp hx

private def nilradicalSubschemeHomeomorph (X : Scheme) :
    (↑X) ≃ₜ (↑(X.nilradical.subscheme)) :=
  (X.nilradical.subschemeι.isEmbedding.toHomeomorphOfSurjective
    (nilradical_subschemeι_surjective X)).symm

private lemma nilradicalSubschemeHomeomorph_subschemeι (X : Scheme) (x : X) :
    X.nilradical.subschemeι (nilradicalSubschemeHomeomorph X x) = x := by
  exact (X.nilradical.subschemeι.isEmbedding.toHomeomorphOfSurjective
    (nilradical_subschemeι_surjective X)).apply_symm_apply x

private def pullback_points_homeomorph_of_residueTensor_subsingleton
    {Y X Z : Scheme} (f : Y ⟶ Z) (g : X ⟶ Z)
    [CompactSpace (↑(pullback f g))] [T2Space Y] [T2Space X]
    (hsub : ∀ T : Scheme.Pullback.Triplet f g, Subsingleton (Spec T.tensor)) :
    (↑(pullback f g)) ≃ₜ {p : Y × X // f.base p.1 = g.base p.2} := by
  let φ : (↑(pullback f g)) → {p : Y × X // f.base p.1 = g.base p.2} := fun t =>
    ⟨((pullback.fst f g).base t, (pullback.snd f g).base t), by
      have h := congrArg (fun k : pullback f g ⟶ Z => k.base t)
        (pullback.condition (f := f) (g := g))
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h⟩
  have hcont : Continuous φ := by
    apply Continuous.subtype_mk
    exact (pullback.fst f g).continuous.prodMk (pullback.snd f g).continuous
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      let E := Scheme.Pullback.carrierEquiv (f := f) (g := g)
      have hpair := congrArg Subtype.val hab
      have ht : (E a).1 = (E b).1 := by
        apply Scheme.Pullback.Triplet.ext
        · simpa [E, Scheme.Pullback.carrierEquiv, Scheme.Pullback.Triplet.ofPoint, φ]
            using congrArg Prod.fst hpair
        · simpa [E, Scheme.Pullback.carrierEquiv, Scheme.Pullback.Triplet.ofPoint, φ]
            using congrArg Prod.snd hpair
      have hE : E a = E b := by
        apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
        exact ⟨ht, Subsingleton.elim _ _⟩
      exact E.injective hE
    · intro p
      rcases p with ⟨⟨y, x⟩, h⟩
      obtain ⟨t, hfst, hsnd⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) y x h
      refine ⟨t, ?_⟩
      apply Subtype.ext
      exact Prod.ext hfst hsnd
  exact IsHomeomorph.homeomorph φ <|
    (isHomeomorph_iff_continuous_bijective).mpr ⟨hcont, hbij⟩

private def split_reduced_pullback_point_product_homeomorph
    {Y X Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Z)
    [CompactSpace (↑(pullback f g))] [T2Space Y] [T2Space X]
    (hsub : ∀ T : Scheme.Pullback.Triplet f g, Subsingleton (Spec T.tensor))
    {m : ℕ}
    (e : (pullback f g).nilradical.subscheme ≅
      ∐ (fun _ : Fin m ↦ X.nilradical.subscheme)) :
    {p : Y × X // f.base p.1 = g.base p.2} ≃ₜ Σ _ : Fin m, X := by
  let hpull := pullback_points_homeomorph_of_residueTensor_subsingleton f g hsub
  let hred := nilradicalSubschemeHomeomorph (pullback f g)
  let he := schemeIsoHomeomorph e
  let hnilX := nilradicalSubschemeHomeomorph X
  let herightHomeo : (Σ _ : Fin m, X) ≃ₜ Σ _ : Fin m, X.nilradical.subscheme := {
    toFun := fun p => ⟨p.1, hnilX p.2⟩
    invFun := fun p => ⟨p.1, hnilX.symm p.2⟩
    left_inv := by rintro ⟨i, x⟩; simp
    right_inv := by rintro ⟨i, x⟩; simp
    continuous_toFun := continuous_sigma fun _ => continuous_sigmaMk.comp hnilX.continuous
    continuous_invFun := continuous_sigma fun _ => continuous_sigmaMk.comp hnilX.symm.continuous
  }
  let C : Scheme.{u} := ∐ (fun _ : Fin m => X.nilradical.subscheme)
  let hcoprod : (Σ _ : Fin m, X.nilradical.subscheme) ≃ₜ (↑C) :=
    schemeSigmaHomeomorph (fun _ : Fin m => X.nilradical.subscheme)
  exact hpull.symm.trans (hred.trans (he.trans (hcoprod.symm.trans herightHomeo.symm)))

private lemma split_reduced_pullback_point_product_homeomorph_snd
    {Y X Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Z)
    [CompactSpace (↑(pullback f g))] [T2Space Y] [T2Space X]
    (hsub : ∀ T : Scheme.Pullback.Triplet f g, Subsingleton (Spec T.tensor))
    {m : ℕ}
    (e : (pullback f g).nilradical.subscheme ≅
      ∐ (fun _ : Fin m ↦ X.nilradical.subscheme))
    (q : (pullback f g).nilradical.subscheme ⟶ X.nilradical.subscheme)
    (hq₁ : q ≫ X.nilradical.subschemeι =
      (pullback f g).nilradical.subschemeι ≫ pullback.snd f g)
    (hq₂ : e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) = q)
    (p : {p : Y × X // f.base p.1 = g.base p.2}) :
    (split_reduced_pullback_point_product_homeomorph f g hsub e p).2 = p.1.2 := by
  let hpull := pullback_points_homeomorph_of_residueTensor_subsingleton f g hsub
  let hred := nilradicalSubschemeHomeomorph (pullback f g)
  let he := schemeIsoHomeomorph e
  let hnilX := nilradicalSubschemeHomeomorph X
  let C : Scheme.{u} := ∐ (fun _ : Fin m => X.nilradical.subscheme)
  let hcoprod : (Σ _ : Fin m, X.nilradical.subscheme) ≃ₜ (↑C) :=
    schemeSigmaHomeomorph (fun _ : Fin m => X.nilradical.subscheme)
  let t : ↑(pullback f g) := hpull.symm p
  let a : ↑((pullback f g).nilradical.subscheme) := hred t
  let b : ↑C := he a
  let z : Σ _ : Fin m, X.nilradical.subscheme := hcoprod.symm b
  show hnilX.symm z.2 = p.1.2
  have hq : e.hom ≫ (Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) ≫
      X.nilradical.subschemeι) =
      (pullback f g).nilradical.subschemeι ≫ pullback.snd f g := by
    rw [← Category.assoc, hq₂, hq₁]
  have hq' := congrFun (congrArg (fun h => h.base) hq) a
  have hqpoint :
      (Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) ≫
        X.nilradical.subschemeι).base b =
        X.nilradical.subschemeι (z.2) := by
    have hz : hcoprod z = (Sigma.ι (fun _ : Fin m ↦ X.nilradical.subscheme) z.1).base z.2 := by
      rcases z with ⟨i, x⟩
      exact schemeSigmaHomeomorph_mk
        (fun _ : Fin m ↦ X.nilradical.subscheme) i x
    rw [← hcoprod.apply_symm_apply b, hz]
    rcases z with ⟨i, x⟩
    show ((Sigma.ι (fun _ : Fin m ↦ X.nilradical.subscheme) i ≫
      Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) ≫
      X.nilradical.subschemeι).base x) = X.nilradical.subschemeι x
    rw [← Category.assoc, Sigma.ι_desc]
    simp
  have hq'' :
      X.nilradical.subschemeι (z.2) =
        X.nilradical.subschemeι (hnilX p.1.2) := by
    calc
      X.nilradical.subschemeι (z.2) =
        (Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) ≫
          X.nilradical.subschemeι).base b := hqpoint.symm
      _ = (pullback.snd f g).base t := by
            show ((e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 X.nilradical.subscheme) ≫
              X.nilradical.subschemeι).base a) = _
            simpa [a, hred, nilradicalSubschemeHomeomorph_subschemeι] using hq'
      _ = p.1.2 := by
            have hpair := congrArg Subtype.val (hpull.apply_symm_apply p)
            change ((pullback.fst f g).base t, (pullback.snd f g).base t) = p.1 at hpair
            exact congrArg Prod.snd hpair
      _ = X.nilradical.subschemeι (hnilX p.1.2) :=
            (nilradicalSubschemeHomeomorph_subschemeι X p.1.2).symm
  have hpoints : z.2 = hnilX p.1.2 := X.nilradical.subschemeι.isEmbedding.injective hq''
  calc
    hnilX.symm z.2 = hnilX.symm (hnilX p.1.2) := congrArg hnilX.symm hpoints
    _ = p.1.2 := hnilX.symm_apply_apply p.1.2

private lemma extremallyDisconnected_preimage_of_split
    {Y X S Z : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [TopologicalSpace S] [TopologicalSpace Z] [CompactSpace S]
    [T2Space Y] [ExtremallyDisconnected S]
    (f : Y → Z) (g : X → S) (s : S → Z) (hs : Function.Injective s)
    {n : ℕ}
    (e : {p : Y × X // f p.1 = s (g p.2)} ≃ₜ Σ _ : Fin n, X)
    (he : ∀ p, (e p).2 = p.1.2)
    (σ : S → X) (hσ : Continuous σ) (hsec : g ∘ σ = id) :
    ExtremallyDisconnected (f ⁻¹' Set.range s) := by
  have hx (z : Σ _ : Fin n, S) : (e.symm ⟨z.1, σ z.2⟩).1.2 = σ z.2 := by
    rw [← he, e.apply_symm_apply]
  have hbase (z : Σ _ : Fin n, S) : f (e.symm ⟨z.1, σ z.2⟩).1.1 = s z.2 := by
    rw [(e.symm ⟨z.1, σ z.2⟩).2, hx]
    exact congrArg s (congrFun hsec z.2)
  let F : (Σ _ : Fin n, S) → (f ⁻¹' Set.range s) := fun z ↦
    ⟨(e.symm ⟨z.1, σ z.2⟩).1.1, ⟨z.2, (hbase z).symm⟩⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp (continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_sigma fun _ ↦ continuous_sigmaMk.comp hσ)))
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      have hxy : x = y := hs ((hbase ⟨i, x⟩).symm.trans
        ((congrArg (fun z ↦ f z.val) h).trans (hbase ⟨j, y⟩)))
      subst y
      have hp : e.symm ⟨i, σ x⟩ = e.symm ⟨j, σ x⟩ := by
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val h
        · rw [← he, ← he, e.apply_symm_apply, e.apply_symm_apply]
      have hij := congrArg (fun z ↦ (e z).1) hp
      simp only [e.apply_symm_apply] at hij
      subst j
      rfl
    · rintro ⟨y, x, hx⟩
      let p : {p : Y × X // f p.1 = s (g p.2)} :=
        ⟨(y, σ x), hx.symm.trans (congrArg s (congrFun hsec x)).symm⟩
      refine ⟨⟨(e p).1, x⟩, ?_⟩
      apply Subtype.ext
      have hp : (⟨(e p).1, σ x⟩ : Σ _ : Fin n, X) = e p := by
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (he p).symm
      show (e.symm ⟨(e p).1, σ x⟩).1.1 = y
      rw [hp, e.symm_apply_apply]
  exact extremallyDisconnected_of_homeo
    (IsHomeomorph.homeomorph F (isHomeomorph_iff_continuous_bijective.mpr ⟨hF, hbij⟩))

/-- The spectrum of a quasi-finite, finitely presented algebra over a ring with separably closed
residue fields and Hausdorff extremally disconnected spectrum is extremally disconnected. -/
@[stacks 0985]
theorem extremallyDisconnected_primeSpectrum_of_quasiFinite
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] [Algebra.FinitePresentation A B]
    (hres : ∀ p : PrimeSpectrum A, IsSepClosed p.asIdeal.ResidueField)
    (hT2 : T2Space (PrimeSpectrum A))
    (hA : ExtremallyDisconnected (PrimeSpectrum A)) :
    ExtremallyDisconnected (PrimeSpectrum B) := by
  let A' := ULift.{max u v} A
  let B' := ULift.{max u v} B
  let : Algebra A' B' := ULift.algebra' A B'
  obtain ⟨hqf', hfp'⟩ := ulift_quasiFinite_and_finitePresentation A B
  let : Algebra.QuasiFinite A' B' := hqf'
  let : Algebra.FinitePresentation A' B' := hfp'
  have hres' : ∀ p : PrimeSpectrum A', IsSepClosed p.asIdeal.ResidueField :=
    ulift_residueField_isSepClosed A hres
  let eA : A' ≃+* A := ULift.ringEquiv
  let eB : B' ≃+* B := ULift.ringEquiv
  let hAhomeo := PrimeSpectrum.homeomorphOfRingEquiv eA
  let hBhomeo := PrimeSpectrum.homeomorphOfRingEquiv eB
  have hA' : ExtremallyDisconnected (PrimeSpectrum A') := by
    let : ExtremallyDisconnected (PrimeSpectrum A) := hA
    exact extremallyDisconnected_of_homeo hAhomeo.symm
  have hT2' : T2Space (PrimeSpectrum A') := hAhomeo.symm.t2Space
  let X : Scheme.{max u v} := Spec (CommRingCat.of A')
  let Y : Scheme.{max u v} := Spec (CommRingCat.of B')
  let f : Y ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap A' B'))
  let : IsAffine X := inferInstance
  let : IsAffine Y := inferInstance
  have hSpec : LocallyOfFiniteType f ∧ LocallyQuasiFinite f ∧
      AlgebraicGeometry.FinitePresentation f := specMap_has_quasiFinite_finitePresentation A' B'
  let : LocallyOfFiniteType f := hSpec.1
  let : LocallyQuasiFinite f := hSpec.2.1
  have hT2X : T2Space (↑X) := hT2'
  let : T2Space (↑X) := hT2X
  let : ExtremallyDisconnected (↑X) := hA'
  obtain ⟨n, S, s, hS, -, hcover, hsplit⟩ :=
    AlgebraicGeometry.exists_finite_affine_stratification_split_reduction f hSpec.2.2
  have : T2Space Y := t2Space_of_affine_quasiFinite f
  have hresX : ∀ x : X, IsSepClosed (X.residueField x) := fun x ↦
    isSepClosed_of_ringEquiv
      (Scheme.Spec.residueFieldIso (CommRingCat.of A') x).commRingCatIsoToRingEquiv.symm
      (hres' x)
  have hclopen (i : Fin n) : IsClopen (Set.range (s i).base) :=
    isClopen_of_isConstructible_of_compact_t2 _ (hS i).2.2.2
  have hED (i : Fin n) : ExtremallyDisconnected (f.base ⁻¹' Set.range (s i).base) := by
    have : IsAffine (S i) := (hS i).1
    have : IsImmersion (s i) := (hS i).2.1
    have : T2Space (S i) := (s i).isEmbedding.t2Space
    have : ExtremallyDisconnected (Set.range (s i).base) :=
      extremallyDisconnected_subtype_of_isOpen _ (hclopen i).isOpen
    have : ExtremallyDisconnected (S i) :=
      extremallyDisconnected_of_homeo (s i).isEmbedding.toHomeomorph.symm
    obtain ⟨S', g, hsurj, hfree, m, q, e, hq₁, hq₂⟩ := hsplit i
    have : Stacks.Morphisms.IsFiniteLocallyFree g := hfree
    have : IsFinite g :=
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
        hfree).1
    have : IsAffine S' := isAffine_of_isAffineHom g
    have : T2Space S' := t2Space_of_affine_quasiFinite g
    have : CompactSpace (↑(pullback f (g ≫ s i))) := inferInstance
    have hsub := pullbackTriplet_subsingleton_of_quasiFinite f (g ≫ s i) hresX
    let ep := split_reduced_pullback_point_product_homeomorph f (g ≫ s i) hsub e
    have hep := split_reduced_pullback_point_product_homeomorph_snd
      f (g ≫ s i) hsub e q hq₁ hq₂
    have hsec : HasContinuousSectionFromCompactT2 (S i) :=
      ((extremallyDisconnected_tfae (S i)).out 1 2
        (a := ExtremallyDisconnected (S i))
        (b := HasContinuousSectionFromCompactT2 (S i))).mp inferInstance
    obtain ⟨σ, hσ, hσg⟩ := hsec g.base g.continuous hsurj.1
    exact extremallyDisconnected_preimage_of_split f.base g.base (s i).base
      (s i).isEmbedding.injective ep hep σ hσ hσg
  have hEDY : ExtremallyDisconnected Y := by
    apply extremallyDisconnected_of_finite_clopen_cover
      (fun i ↦ f.base ⁻¹' Set.range (s i).base)
      (fun i ↦ (hclopen i).isOpen.preimage f.continuous)
      (fun i ↦ (hclopen i).isClosed.preimage f.continuous)
      _ hED
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  have : ExtremallyDisconnected (PrimeSpectrum B') := hEDY
  exact extremallyDisconnected_of_homeo hBhomeo
end AlgebraicGeometry.ProEtale

end

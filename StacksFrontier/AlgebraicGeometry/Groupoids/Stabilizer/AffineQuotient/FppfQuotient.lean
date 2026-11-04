module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient.LocalInvariants

/-!
# Finite flat equivalence relations on affine schemes

Let a groupoid scheme over `S` have affine object and arrow schemes and finite locally free
source and target maps, and let its arrow scheme be an equivalence relation on the object
scheme. Then the spectrum of the ring of invariant functions is the fppf quotient of the
object scheme by the relation: the canonical morphism to it is finite locally free, the
relation is its kernel pair, and it represents the quotient sheaf on a big fppf site.

## Main definitions

* `AlgebraicGeometry.quotientBaseMap` is the structure morphism of the invariant spectrum over
  `S`, obtained by descending the structure morphism of the object scheme.
* `AlgebraicGeometry.quotientOver` and `AlgebraicGeometry.quotientProjection` package the
  invariant spectrum and the canonical morphism to it as an object and a morphism of `Over S`.

## Main results

* `AlgebraicGeometry.objectsToInvariantSpectrum_isFiniteLocallyFree`: the canonical morphism to
  the invariant spectrum is finite locally free.
* `AlgebraicGeometry.isPullback_objectsToInvariantSpectrum`: the target and source maps exhibit
  the arrow scheme as the kernel pair of that morphism.
* `AlgebraicGeometry.quotientSheaf_isRepresented`: the invariant spectrum over `S` represents
  the fppf quotient sheaf of the relation, compatibly with the canonical projection.

## Implementation notes

The quotient scheme and the quotient morphism are `Spec (.of (invariantRing G))` and
`AlgebraicGeometry.objectsToInvariantSpectrum`, the constructions of Tag 03BL. Descent of the
structure morphism to `S` is packaged as a specified morphism out of that spectrum rather than
as an existence statement, so that the object and the morphism of `Over S` built from it are
canonical. The kernel-pair claim is expressed as a pullback square, not as an unspecified
isomorphism. The representation of the quotient sheaf is the canonical isomorphism out of the
sheafification of the presheaf quotient, together with its compatibility with the quotient
projection.

A big fppf site is chosen as in Tag 021S, and the functor of points is restricted along its
inclusion; this avoids an extra size assumption on the invariant spectrum. That the restricted
functor of points of a scheme over `S` is a sheaf for the localized topology is deduced from
subcanonicity of the fpqc topology, by checking that the inclusion of the big site is
cover-preserving and representably flat.

The core of the argument is local on the invariant ring: after a flat base change to a local
ring with infinite residue field, semilocality of the object ring lets the basis of Tag 03C8 be
chosen among the images of the target map, which makes the comparison `A ⊗_C A ≅ B` an
isomorphism; finite locally freeness and the kernel-pair property then descend along the
faithfully flat base change.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms AlgebraicGeometry.GroupoidScheme

private lemma objectsToInvariantSpectrum_isFiniteLocallyFree_of_basis
    {S : Scheme.{u}} (G : GroupoidScheme S) [IsAffine G.objects.left]
    {n : ℕ} (b : Module.Basis (Fin n) (invariantRing G) Γ(G.objects.left, ⊤)) :
    IsFiniteLocallyFree (objectsToInvariantSpectrum G) := by
  let q := Spec.map (CommRingCat.ofHom (invariantRing G).subtype)
  have hq : IsFiniteLocallyFree q :=
    specMap_isFiniteLocallyFree_of_moduleBasis _ _ _ b
  show IsFiniteLocallyFree (G.objects.left.isoSpec.hom ≫ q)
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFiniteLocallyFree _ _).mpr hq

private lemma isPullback_objectsToInvariantSpectrum_of_tensorEquiv
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    (e : RingEquiv (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))
      Γ(G.arrows.left, ⊤))
    (he : ∀ a a', e (a ⊗ₜ[invariantRing G] a') = sourceMap G a * targetMap G a') :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) := by
  let A := Γ(G.objects.left, ⊤)
  let C := invariantRing G
  have hpush : IsPushout (CommRingCat.ofHom C.subtype) (CommRingCat.ofHom C.subtype)
      G.source.left.appTop G.target.left.appTop := by
    apply (CommRingCat.isPushout_tensorProduct C A A).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
    · rfl
    · rfl
    · apply CommRingCat.hom_ext
      ext a
      show e (a ⊗ₜ[C] 1) = sourceMap G a
      rw [he, map_one, mul_one]
    · apply CommRingCat.hom_ext
      ext a
      show e (1 ⊗ₜ[C] a) = targetMap G a
      rw [he, map_one, one_mul]
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  apply IsPullback.flip
  apply hpb.of_iso' G.arrows.left.isoSpec G.objects.left.isoSpec
    G.objects.left.isoSpec (Iso.refl _)
  · exact Scheme.isoSpec_hom_naturality G.source.left
  · exact Scheme.isoSpec_hom_naturality G.target.left
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

private lemma finiteLocallyFree_and_isPullback_of_local_invariants
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    [IsLocalRing (invariantRing G)]
    [Infinite (IsLocalRing.ResidueField (invariantRing G))] :
    IsFiniteLocallyFree (objectsToInvariantSpectrum G) ∧
      IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) := by
  obtain ⟨n, b, e, he⟩ := exists_basis_and_tensorEquiv_of_local_invariants G
  exact ⟨objectsToInvariantSpectrum_isFiniteLocallyFree_of_basis G b,
    isPullback_objectsToInvariantSpectrum_of_tensorEquiv G e he⟩

private lemma baseChange_isEquivalenceRelation
    {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (H : AffineInvariantBaseChange G C') :
    IsEquivalenceRelation H.groupoid.target H.groupoid.source := by
  have hm {T : Over (Spec (.of C'))} (f g : T ⟶ H.groupoid.arrows)
      (ht : f ≫ H.groupoid.target = g ≫ H.groupoid.target)
      (hs : f ≫ H.groupoid.source = g ≫ H.groupoid.source) : f = g := by
    apply Over.OverMorphism.ext
    apply H.arrows_isPullback.hom_ext
    · apply arrows_hom_ext G
      · have he := congrArg (fun k : T ⟶ H.groupoid.objects ↦
          k.left ≫ H.objectsProjection) ht
        simpa only [Over.comp_left, Category.assoc, ← H.projection_target] using he
      · have he := congrArg (fun k : T ⟶ H.groupoid.objects ↦
          k.left ≫ H.objectsProjection) hs
        simpa only [Over.comp_left, Category.assoc, ← H.projection_source] using he
    · exact (Over.w f).trans (Over.w g).symm
  exact ⟨⟨{
    right_cancellation := fun {T} f g ht hs ↦ hm f g ht hs
    r := H.groupoid.identity
    reflexivity₁ := H.groupoid.target_identity
    reflexivity₂ := H.groupoid.source_identity
    s := H.groupoid.inverse
    symmetry₁ := H.groupoid.target_inverse
    symmetry₂ := H.groupoid.source_inverse
    c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    isLimit := (IsPullback.of_hasPullback _ _).isLimit
    t := H.groupoid.comp
    transitivity₁ := H.groupoid.target_comp
    transitivity₂ := H.groupoid.source_comp }⟩⟩

private lemma objectsToInvariantSpectrum_comp_invariantSpectrumMap
    {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (H : AffineInvariantBaseChange G C') :
    objectsToInvariantSpectrum H.groupoid ≫
        Spec.map (CommRingCat.ofHom H.canonicalMapToInvariantFunctions) =
      H.groupoid.objects.hom := by
  unfold objectsToInvariantSpectrum
  rw [Category.assoc, ← Spec.map_comp]
  show H.groupoid.objects.left.toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (.of C')).inv ≫ H.groupoid.objects.hom.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  simp

private lemma baseChange_finiteLocallyFree_and_isPullback
    {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (H : AffineInvariantBaseChange G C') :
    IsFiniteLocallyFree H.groupoid.objects.hom ∧
      IsPullback H.groupoid.target.left H.groupoid.source.left
        H.groupoid.objects.hom H.groupoid.objects.hom := by
  let : IsAffine H.groupoid.objects.left :=
    (IsAffine.iff_of_isIso H.objectsIso.hom).mpr inferInstance
  let : IsAffine H.groupoid.arrows.left :=
    (IsAffine.iff_of_isIso H.arrowsIso.hom).mpr inferInstance
  let : IsFiniteLocallyFree H.groupoid.source.left := H.source_isFiniteLocallyFree
  let : IsFiniteLocallyFree H.groupoid.target.left := H.target_isFiniteLocallyFree
  let : IsEquivalenceRelation H.groupoid.target H.groupoid.source :=
    baseChange_isEquivalenceRelation H
  let e := RingEquiv.ofBijective H.canonicalMapToInvariantFunctions
    (AlgebraicGeometry.canonicalMapToInvariantFunctions_bijective_of_flat H)
  let : IsLocalRing (invariantRing H.groupoid) := e.isLocalRing
  let : IsLocalHom e.toRingHom := isLocalHom_toRingHom e
  let : Infinite (IsLocalRing.ResidueField (invariantRing H.groupoid)) :=
    Infinite.of_injective (IsLocalRing.ResidueField.map e.toRingHom)
      (RingHom.injective _)
  obtain ⟨hf, hp⟩ := finiteLocallyFree_and_isPullback_of_local_invariants H.groupoid
  let k := Spec.map (CommRingCat.ofHom H.canonicalMapToInvariantFunctions)
  let hk : IsIso k := by
    show IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  have hcomp : objectsToInvariantSpectrum H.groupoid ≫ k = H.groupoid.objects.hom :=
    objectsToInvariantSpectrum_comp_invariantSpectrumMap H
  refine ⟨?_, ?_⟩
  · rw [← hcomp]
    exact (MorphismProperty.cancel_right_of_respectsIso @IsFiniteLocallyFree _ k).mpr hf
  · apply hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (@asIso _ _ _ _ k hk)
    · simp
    · simp
    · simpa using hcomp
    · simpa using hcomp

private lemma baseChange_module_flat
    {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (H : AffineInvariantBaseChange G C') :
    Module.Flat C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤)) := by
  obtain ⟨hf, _⟩ := baseChange_finiteLocallyFree_and_isPullback H
  have hfl : Flat H.groupoid.objects.hom :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      H.groupoid.objects.hom).mp hf).2.1
  have he : (objectSchemeBaseChange G C').hom =
      H.objectsIso.inv ≫ H.groupoid.objects.hom := by
    rw [← H.objectsIso_over]
    exact (Iso.inv_hom_id_assoc _ _).symm
  have hcomp : Flat (H.objectsIso.inv ≫ H.groupoid.objects.hom) :=
    Flat.comp _ _ (hg := hfl)
  have hobj : Flat (objectSchemeBaseChange G C').hom := he ▸ hcomp
  let e := (Algebra.TensorProduct.comm (invariantRing G) Γ(G.objects.left, ⊤) C').toRingEquiv
  have hq : Spec.map (CommRingCat.ofHom
      (algebraMap C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤)))) =
      Spec.map e.toCommRingCatIso.hom ≫ (objectSchemeBaseChange G C').hom := by
    dsimp [objectSchemeBaseChange]
    rw [← Spec.map_comp]
    congr 1
  have hflat' : Flat (Spec.map e.toCommRingCatIso.hom ≫ (objectSchemeBaseChange G C').hom) :=
    Flat.comp _ _ (hg := hobj)
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤))))) := hq ▸ hflat'
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)

/-- At any prime of the invariant ring there is a flat local base change `C'` of the invariant
ring with infinite residue field, faithfully flat over the localization, carrying a base change
of the groupoid. -/
private lemma exists_local_baseChange_over_localization
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (p : Ideal (invariantRing G)) [p.IsPrime] :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra (invariantRing G) C')
      (_ : Algebra (Localization.AtPrime p) C')
      (_ : IsScalarTower (invariantRing G) (Localization.AtPrime p) C')
      (_ : Module.Flat (invariantRing G) C') (_ : IsLocalRing C')
      (_ : Infinite (IsLocalRing.ResidueField C'))
      (_ : Module.FaithfullyFlat (Localization.AtPrime p) C'),
      Nonempty (AffineInvariantBaseChange G C') := by
  obtain ⟨C', hComm, hAlg, hLocal, hHom, hflat, hmax, hres, hinf⟩ :=
    exists_flat_local_algebra_with_infinite_residueField (Localization.AtPrime p)
  let : CommRing C' := hComm
  let : Algebra (Localization.AtPrime p) C' := hAlg
  let : IsLocalRing C' := hLocal
  let : IsLocalHom (algebraMap (Localization.AtPrime p) C') := hHom
  let : Module.Flat (Localization.AtPrime p) C' := hflat
  let : Algebra (invariantRing G) C' :=
    ((algebraMap (Localization.AtPrime p) C').comp (algebraMap (invariantRing G) _)).toAlgebra
  let : IsScalarTower (invariantRing G) (Localization.AtPrime p) C' :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨C', _, _, _, inferInstance, Module.Flat.trans _ (Localization.AtPrime p) C', _, hinf,
    Module.FaithfullyFlat.of_flat_of_isLocalHom, exists_affineInvariantBaseChange G C'⟩

private lemma quotient_module_flat
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    Module.Flat (invariantRing G) Γ(G.objects.left, ⊤) := by
  let A := Γ(G.objects.left, ⊤)
  let C := invariantRing G
  apply (flat_iff_forall_flat_atPrime A).mpr
  intro p hp
  let := hp
  let Cp := Localization.AtPrime p
  obtain ⟨C', _, _, _, _, _, _, _, _, ⟨H⟩⟩ := exists_local_baseChange_over_localization G p
  let : Module.Flat C' (C' ⊗[C] A) := baseChange_module_flat H
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange C Cp C' C' A
  have hbc : Module.Flat C' (C' ⊗[Cp] (Cp ⊗[C] A)) :=
    (Module.Flat.equiv_iff e).mpr inferInstance
  have hCp : Module.Flat Cp (Cp ⊗[C] A) :=
    (Module.Flat.iff_flat_tensorProduct Cp (Cp ⊗[C] A) C').mp hbc
  exact (Module.Flat.equiv_iff (LocalizedModule.equivTensorProduct p.primeCompl A)).mpr hCp

private lemma baseChange_tensorMap_injective
    {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (H : AffineInvariantBaseChange G C') :
    letI := invariantRingAlgebraArrow G
    let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _)
    Function.Injective (Algebra.TensorProduct.map φ (AlgHom.id (invariantRing G) C')) := by
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let := invariantRingAlgebraArrow G
  let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _)
  let s' := CommRingCat.ofHom
    (Algebra.TensorProduct.map (sourceAlgHom G) (AlgHom.id C C')).toRingHom
  let t' := CommRingCat.ofHom
    (Algebra.TensorProduct.map (targetAlgHom G) (AlgHom.id C C')).toRingHom
  let i := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : C' →ₐ[C] A ⊗[C] C').toRingHom
  have hp : IsPushout i i s' t' := by
    apply IsPullback.unop
    apply IsPullback.of_map_of_faithful Scheme.Spec
    apply (baseChange_finiteLocallyFree_and_isPullback H).2.of_iso
      H.arrowsIso H.objectsIso H.objectsIso (Iso.refl _)
    · rw [H.target_eq]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      congr 2
    · rw [H.source_eq]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      congr 2
    · simpa [objectSchemeBaseChange] using H.objectsIso_over.symm
    · simpa [objectSchemeBaseChange] using H.objectsIso_over.symm
  let l := CommRingCat.ofHom
    (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] A) (AlgHom.id C C')).toRingHom
  let r := CommRingCat.ofHom
    (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeRight : A →ₐ[C] A ⊗[C] A) (AlgHom.id C C')).toRingHom
  have hw : i ≫ l = i ≫ r := by
    ext c
    simp [i, l, r]
  let ψ := hp.desc l r hw
  have hs (a : A ⊗[C] C') : ψ (s' a) = l a :=
    congrArg (fun f : CommRingCat.of (A ⊗[C] C') ⟶ _ ↦ f a) (hp.inl_desc l r hw)
  have ht (a : A ⊗[C] C') : ψ (t' a) = r a :=
    congrArg (fun f : CommRingCat.of (A ⊗[C] C') ⟶ _ ↦ f a) (hp.inr_desc l r hw)
  have he (z : (A ⊗[C] A) ⊗[C] C') :
      ψ ((Algebra.TensorProduct.map φ (AlgHom.id C C')) z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d c =>
      induction d using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul a b =>
        have hab : (Algebra.TensorProduct.map φ (AlgHom.id C C'))
            ((a ⊗ₜ[C] b) ⊗ₜ[C] c) = s' (a ⊗ₜ[C] c) * t' (b ⊗ₜ[C] 1) := by
          simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
            AlgHom.toRingHom_eq_coe, ConcreteCategory.hom_ofHom, RingHom.coe_coe,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, φ, s', t']
          exact congrArg (fun z : B ↦ z ⊗ₜ[C] c)
            (Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
              (fun _ _ ↦ Commute.all _ _) a b)
        rw [hab, map_mul, hs, ht]
        simp only [AlgHom.toRingHom_eq_coe, ConcreteCategory.hom_ofHom, RingHom.coe_coe,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply, AlgHom.coe_id,
          id_eq, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, l, r]
  exact Function.LeftInverse.injective he

/-- An element of `A ⊗_C A` annihilated by the comparison map to the arrow ring stays
annihilated after a flat local base change of the invariant ring with infinite residue
field. -/
private lemma tmul_one_eq_zero_of_tensorLift_eq_zero
    {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (H : AffineInvariantBaseChange G C')
    (x : Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))
    (hx : letI := invariantRingAlgebraArrow G
      Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
        (fun _ _ ↦ Commute.all _ _) x = 0) :
    x ⊗ₜ[invariantRing G] (1 : C') = 0 := by
  let := invariantRingAlgebraArrow G
  apply baseChange_tensorMap_injective H
  show (Algebra.TensorProduct.map
      (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
        (fun _ _ ↦ Commute.all _ _)) (AlgHom.id (invariantRing G) C'))
      (x ⊗ₜ[invariantRing G] 1) = _
  simp [hx]

/-- In a tower `C → Cp → C'` of commutative rings, a class of a `C`-module `D` that dies in
`D ⊗_C C'` also dies in `C' ⊗_Cp (Cp ⊗_C D)`. -/
private lemma one_tmul_baseChange_eq_zero_of_tmul_one_eq_zero
    {C Cp C' D : Type u} [CommRing C] [CommRing Cp] [CommRing C']
    [Algebra C Cp] [Algebra Cp C'] [Algebra C C'] [IsScalarTower C Cp C']
    [AddCommGroup D] [Module C D] {x : D} (hz : x ⊗ₜ[C] (1 : C') = 0) :
    (1 : C') ⊗ₜ[Cp] ((1 : Cp) ⊗ₜ[C] x) = 0 := by
  have hz' : (1 : C') ⊗ₜ[C] x = 0 := by
    simpa using congrArg (TensorProduct.comm C D C') hz
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange C Cp C' C' D).injective
  simpa using hz'

/-- Localized at any maximal ideal of the invariant ring, a class in `A ⊗_C A` annihilated by
the comparison map to the arrow ring vanishes. -/
private lemma tensorLift_tmul_one_eq_zero_at_maximal
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (x : Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))
    (hx : letI := invariantRingAlgebraArrow G
      Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
        (fun _ _ ↦ Commute.all _ _) x = 0)
    (p : Ideal (invariantRing G)) [p.IsMaximal] :
    (1 : Localization.AtPrime p) ⊗ₜ[invariantRing G] x = 0 := by
  obtain ⟨C', _, _, _, _, _, _, _, _, ⟨H⟩⟩ := exists_local_baseChange_over_localization G p
  let A := Γ(G.objects.left, ⊤)
  let C := invariantRing G
  let D := A ⊗[C] A
  let Cp := Localization.AtPrime p
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff Cp (Cp ⊗[C] D) _).mp
    (one_tmul_baseChange_eq_zero_of_tmul_one_eq_zero
      (tmul_one_eq_zero_of_tensorLift_eq_zero H x hx))

private lemma tensorMap_injective
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    letI := invariantRingAlgebraArrow G
    Function.Injective (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _)) := by
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let D := A ⊗[C] A
  let := invariantRingAlgebraArrow G
  let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _)
  apply (injective_iff_map_eq_zero φ).mpr
  intro x hx
  apply Module.eq_zero_of_localization_maximal
    (fun p _ ↦ Localization.AtPrime p ⊗[C] D)
    (fun p _ ↦ TensorProduct.mk C (Localization.AtPrime p) D 1) x
  exact fun p _ ↦ tensorLift_tmul_one_eq_zero_at_maximal G x hx p

private lemma quotient_kernelPair
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) := by
  let := invariantRingAlgebraArrow G
  let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _)
  let e := RingEquiv.ofBijective φ.toRingHom
    ⟨tensorMap_injective G, tensorMap_surjective G⟩
  exact isPullback_objectsToInvariantSpectrum_of_tensorEquiv G e fun a b ↦
    Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _) a b

private lemma objectsToInvariantSpectrum_flat
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : Flat (objectsToInvariantSpectrum G) := by
  let := quotient_module_flat G
  let q := Spec.map (CommRingCat.ofHom (invariantRing G).subtype)
  let : Flat q := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (quotient_module_flat G))
  show Flat (G.objects.left.isoSpec.hom ≫ q)
  infer_instance

private lemma objectsToInvariantSpectrum_finite
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : IsFinite (objectsToInvariantSpectrum G) := by
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let : Algebra A B := (sourceMap G).toAlgebra
  let := invariantRingAlgebraArrow G
  let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _)
  let φA : (A ⊗[C] A) →ₐ[A] B :=
    { toRingHom := φ.toRingHom
      commutes' := fun a ↦ by
        show φ (a ⊗ₜ[C] 1) = sourceMap G a
        exact (Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
          (fun _ _ ↦ Commute.all _ _) a 1).trans (by rw [map_one, mul_one]; rfl) }
  let e := AlgEquiv.ofBijective φA ⟨tensorMap_injective G, tensorMap_surjective G⟩
  let : IsFinite G.source.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      inferInstance |>.1
  let : Module.Finite A B := G.source.left.finite_appTop
  let : Module.Finite A (A ⊗[C] A) := Module.Finite.equiv e.symm.toLinearEquiv
  let q := Spec.map (CommRingCat.ofHom C.subtype)
  let : Flat q := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (quotient_module_flat G))
  let : Surjective q := ⟨fun x ↦
    let ⟨y, hy⟩ := AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum G x
    ⟨G.objects.left.isoSpec.hom y, hy⟩⟩
  let : Module.FaithfullyFlat C A :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom C.subtype)).mp
        ⟨inferInstance, inferInstance⟩)
  let : Module.Finite C A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A
  let : IsFinite q := (IsFinite.SpecMap_iff _).mpr (inferInstanceAs (Module.Finite C A))
  show IsFinite (G.objects.left.isoSpec.hom ≫ q)
  infer_instance

private theorem relation_factors_quotient {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    G.target.left ≫ objectsToInvariantSpectrum G = G.source.left ≫ objectsToInvariantSpectrum G :=
    (source_comp_objectsToInvariantSpectrum G).symm

/-- The canonical map to the spectrum of invariant functions is finite locally free. -/
@[stacks 03BM "finite locally free quotient map"]
public instance objectsToInvariantSpectrum_isFiniteLocallyFree {S : Scheme.{u}}
    (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    IsFiniteLocallyFree (objectsToInvariantSpectrum G) := by
  let : Flat (objectsToInvariantSpectrum G) := objectsToInvariantSpectrum_flat G
  let : IsFinite (objectsToInvariantSpectrum G) := objectsToInvariantSpectrum_finite G
  let : Surjective (objectsToInvariantSpectrum G) :=
    ⟨AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum G⟩
  let : LocallyOfFinitePresentation G.target.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      inferInstance |>.2.2
  have hp := quotient_kernelPair G
  have hfp : LocallyOfFinitePresentation (objectsToInvariantSpectrum G) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨inferInstance, inferInstance, hfp⟩

/-- The source and target maps exhibit the arrow scheme as the kernel pair of the quotient. -/
@[stacks 03BM "the relation is the kernel pair"]
public theorem isPullback_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) :=
  quotient_kernelPair G

/-- The map from the affine invariant quotient to the base scheme, specified by descent of
the original structure map. -/
@[stacks 03BM "descent of the quotient over the base"]
public def quotientBaseMap {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    { f : Spec (.of (invariantRing G)) ⟶ S //
        objectsToInvariantSpectrum G ≫ f = G.objects.hom } := by
  let π := objectsToInvariantSpectrum G
  let : IsFiniteLocallyFree π := objectsToInvariantSpectrum_isFiniteLocallyFree G
  have hπ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation π).mp
      (objectsToInvariantSpectrum_isFiniteLocallyFree G)
  let : IsFinite π := hπ.1
  let : Flat π := hπ.2.1
  have hsurj : Function.Surjective π.base :=
    AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum G
  let : Surjective π := (surjective_iff π).2 hsurj
  let : Flat π := inferInstance
  let : QuasiCompact π := inferInstance
  let : EffectiveEpi π := by infer_instance
  let hcompat : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ G.objects.left),
      g₁ ≫ π = g₂ ≫ π → g₁ ≫ G.objects.hom = g₂ ≫ G.objects.hom := by
    intro W g₁ g₂ h
    let r := (isPullback_objectsToInvariantSpectrum G).lift g₁ g₂ h
    have h₁ := (isPullback_objectsToInvariantSpectrum G).lift_fst g₁ g₂ h
    have h₂ := (isPullback_objectsToInvariantSpectrum G).lift_snd g₁ g₂ h
    calc
      g₁ ≫ G.objects.hom = (r ≫ G.target.left) ≫ G.objects.hom := by rw [← h₁]
      _ = r ≫ G.arrows.hom := by
        rw [Category.assoc, ← G.target.w]
      _ = (r ≫ G.source.left) ≫ G.objects.hom := by
        rw [Category.assoc, ← G.source.w]
      _ = g₂ ≫ G.objects.hom := by rw [← h₂]
  refine ⟨EffectiveEpi.desc π G.objects.hom hcompat, ?_⟩
  exact EffectiveEpi.fac π G.objects.hom hcompat

/-- The spectrum of invariant functions as a scheme over the original base. -/
public def quotientOver {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : Over S :=
  Over.mk (quotientBaseMap G).val

/-- The canonical projection to the invariant quotient over the base scheme. -/
public def quotientProjection {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] : G.objects ⟶ quotientOver G :=
  Over.homMk (objectsToInvariantSpectrum G) (quotientBaseMap G).property

/-- The scheme underlying `quotientOver G` is the spectrum of invariant functions. -/
@[simp]
public theorem quotientOver_left {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    (quotientOver G).left = Spec (.of (invariantRing G)) := rfl

/-- The morphism of schemes underlying `quotientProjection G` is the canonical morphism to the
spectrum of invariant functions. -/
@[simp]
public theorem quotientProjection_left {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    (quotientProjection G).left = objectsToInvariantSpectrum G := rfl

private theorem relation_isPullback_over {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target G.source (quotientProjection G) (quotientProjection G) := by
  have hcomm : G.target ≫ quotientProjection G = G.source ≫ quotientProjection G :=
    Over.OverMorphism.ext (relation_factors_quotient G)
  exact (isPullback_objectsToInvariantSpectrum G).of_map (Over.forget S) hcomm

/-- The spectrum of invariant functions represents the fppf quotient sheaf, with the
representing isomorphism compatible with the canonical projection from the objects. -/
@[stacks 03BM "representation of the fppf quotient sheaf"]
public theorem quotientSheaf_isRepresented {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)] :
    let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := AlgebraicGeometry.BigFppfOver.topology B S hS
    let j : Stacks.Groupoids.PreRelation G.arrows G.objects := prod.lift G.target G.source
    ∃ hM : Presheaf.IsSheaf J (Stacks.Groupoids.points F (quotientOver G)),
      ∃ q : Stacks.Groupoids.quotientSheaf J F j ⟶
          (⟨Stacks.Groupoids.points F (quotientOver G), hM⟩ : Sheaf J (Type u)),
        IsIso q ∧
          Stacks.Groupoids.toQuotientSheaf J F j ≫ q.hom =
            F.op.whiskerLeft (yoneda.map (quotientProjection G)) := by
  classical
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let j : Stacks.Groupoids.PreRelation G.arrows G.objects := prod.lift G.target G.source
  let f : G.objects ⟶ quotientOver G := quotientProjection G
  have hf : j.target ≫ f = j.source ≫ f := by
    apply Over.OverMorphism.ext
    simpa [j, Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source, f,
      quotientProjection_left] using relation_factors_quotient G
  let : IsFiniteLocallyFree f.left := by
    simpa [f, quotientProjection_left] using objectsToInvariantSpectrum_isFiniteLocallyFree G
  have hπ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f.left).mp
      (inferInstance : IsFiniteLocallyFree f.left)
  let : Flat f.left := hπ.2.1
  let : LocallyOfFinitePresentation f.left := hπ.2.2
  have hsurj := AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum G
  let : Surjective f.left := (surjective_iff (objectsToInvariantSpectrum G)).2 hsurj
  have hM : Presheaf.IsSheaf J (Stacks.Groupoids.points F (quotientOver G)) :=
    bigFppfOver_points_isSheaf B S hS (quotientOver G)
  have hU := points_map_isLocallySurjective_of_fppf B S hS f
  let k : G.arrows ⟶ pullback f f := pullback.lift j.target j.source hf
  have hk : IsIso k := by
    let hpb := relation_isPullback_over G
    let e := hpb.isoIsPullback G.objects G.objects (IsPullback.of_hasPullback f f)
    have he : e.hom = k := by
      apply pullback.hom_ext
      · calc
          e.hom ≫ pullback.fst f f = G.target := by
            simp [e]
          _ = pullback.lift j.target j.source hf ≫ pullback.fst f f := by
            rw [pullback.lift_fst]
            simp [j, Stacks.Groupoids.PreRelation.target]
      · calc
          e.hom ≫ pullback.snd f f = G.source := by
            simp [e]
          _ = pullback.lift j.target j.source hf ≫ pullback.snd f f := by
            rw [pullback.lift_snd]
            simp [j, Stacks.Groupoids.PreRelation.source]
    rw [← he]
    infer_instance
  let : IsIso k.left := by
    show IsIso ((Over.forget S).map k)
    infer_instance
  let : Flat k.left := by infer_instance
  let : LocallyOfFinitePresentation k.left := by infer_instance
  let : Surjective k.left := by infer_instance
  have hR := points_map_isLocallySurjective_of_fppf B S hS k
  obtain ⟨q, hq, hfac⟩ :=
    Stacks.Groupoids.quotientSheaf_isRepresentedBy_of_locallySurjective J F j f hf hM hU hR
  exact ⟨hM, q, hq, hfac⟩

end AlgebraicGeometry

end

end

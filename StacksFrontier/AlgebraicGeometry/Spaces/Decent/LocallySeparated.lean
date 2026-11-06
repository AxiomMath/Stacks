module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.LocallyClosedImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.InfiniteResidueFields
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Locally separated algebraic spaces are decent

Every point of a locally separated algebraic space over a scheme `S` has a field-valued
representative whose two self-intersection projections are étale and quasi-compact, and the
base change of a *monomorphic* field-valued representative of such a space along an affine
étale chart is finite. Together these two statements make such a space decent, which is
Stacks 088J.

Both statements go through the self-intersection `R = u ×_X u` of the residue-field point `u`
of an étale chart: local separatedness makes `R ⟶ u × u` an immersion, hence a closed
immersion because it is the relation of a groupoid over a field, so `R` is affine; and `R` is
étale over `u` because it factors as a monomorphism followed by an étale morphism. An affine
scheme étale over the spectrum of a field is a finite disjoint union of spectra of finite
separable extensions, and the number of summands in the base change along a chart is finite
because an infinite family of residue fields would put a point of the diagonal in the closure
of the off-diagonal part of the relation.

## Main results

* `AlgebraicGeometry.Space.hasEtaleQuasiCompactFieldRepresentative_of_isLocallySeparatedOver`:
  every point of a locally separated algebraic space satisfies condition (3) of Stacks 03JU.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_isLocallySeparatedOver`:
  a locally separated algebraic space has property `(β)` of Stacks 03JX.
* `AlgebraicGeometry.Space.isFinite_of_isPullback_fieldMorphism_of_isLocallySeparatedOver` and
  `AlgebraicGeometry.Space.isFinite_pullback_fieldMorphism_of_isLocallySeparatedOver`: on a
  locally separated algebraic space, the base change of a monomorphism from the spectrum of a
  field along an affine étale chart is finite.
* `AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyLocallySeparated`: **Stacks 088J**, a
  locally separated algebraic space is decent, and
  `AlgebraicGeometry.Space.isDecentSpace_of_isLocallySeparatedOver` the same under the weaker
  hypothesis of local separatedness over the base scheme.

## Implementation notes

Stacks 088J is assembled from the first and the third of the results above. The first supplies
condition (3) of Stacks 03JU at every point, which the implication from condition (3) to
condition (4) of that tag — in
`StacksFrontier/AlgebraicGeometry/Spaces/MonomorphicFieldRepresentative.lean` — turns into a
monomorphic field-valued representative; the third makes that representative quasi-compact
through the criterion of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactFieldRepresentative.lean`, which is
condition (3) of Stacks 03JV. The outcome is condition (4) of Stacks 03JV, which is how
decency is spelled in `AlgebraicGeometry.Space.IsDecentSpace`.

The hypothesis used below is local separatedness *over the base scheme* `S`, Stacks 02X5, not
the absolute condition of Stacks 03BS; the absolute condition gives it by Stacks 04ZI, and the
relative one is the weaker hypothesis.

The finiteness argument needs the relation of an étale chart to be described by a ring map out
of `A ⊗ℤ A`, so the product `Spec A × Spec A` is identified with `Spec (A ⊗ℤ A)` through the
coproduct of commutative rings; the off-diagonal part of the relation is then the union of the
ranges of `AlgebraicGeometry.Space.Decent.residuePairMap` and the diagonal is the range of
`AlgebraicGeometry.Space.Decent.diagonalMap`, which is the shape Stacks 088I is stated in.

## References

* [Stacks Project, Tag 088I](https://stacks.math.columbia.edu/tag/088I)
* [Stacks Project, Tag 088J](https://stacks.math.columbia.edu/tag/088J)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry

/-! ### The diagonal of a kernel pair -/

/-- A kernel pair of `f : U ⟶ X` is the fibre product of the diagonal of `X` with
`f × f`. -/
private theorem isPullback_diagonal_of_kernelPair
    {C : Type*} [Category* C] {R U X : C}
    [HasBinaryProduct U U] [HasBinaryProduct X X]
    {s t : R ⟶ U} {f : U ⟶ X} (h : IsPullback s t f f) :
    IsPullback (s ≫ f) (prod.lift s t) (diag X) (prod.map f f) := by
  have hw : (s ≫ f) ≫ diag X = prod.lift s t ≫ prod.map f f := by
    apply prod.hom_ext <;> simp [h.w]
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk hw (fun c ↦ h.lift (c.snd ≫ prod.fst)
    (c.snd ≫ prod.snd) ?_) ?_ ?_ ?_
  · have hfst := congrArg (fun m ↦ m ≫ prod.fst) c.condition
    have hsnd := congrArg (fun m ↦ m ≫ prod.snd) c.condition
    simp at hfst hsnd
    simpa only [Category.assoc] using hfst.symm.trans hsnd
  · intro c
    rw [← Category.assoc, h.lift_fst]
    simpa using (congrArg (fun m ↦ m ≫ prod.fst) c.condition).symm
  · intro c
    apply prod.hom_ext <;> simp
  · intro c m hm₁ hm₂
    apply h.hom_ext
    · simpa using congrArg (fun a ↦ a ≫ prod.fst) hm₂
    · simpa using congrArg (fun a ↦ a ≫ prod.snd) hm₂

/-! ### An immersed equivalence relation over a field is a closed immersion -/

/-- The codiscrete groupoid on an object: all pairs of points are arrows. -/
private noncomputable def pairGroupoid {S : Scheme.{u}} (U : Over S) :
    GroupoidScheme S where
  objects := U
  arrows := U ⨯ U
  source := prod.snd
  target := prod.fst
  comp := prod.lift (pullback.fst prod.snd prod.fst ≫ prod.fst)
    (pullback.snd prod.snd prod.fst ≫ prod.snd)
  identity := diag U
  inverse := (prod.braiding U U).hom
  source_identity := by simp
  target_identity := by simp
  source_inverse := by simp
  target_inverse := by simp
  source_comp := by simp
  target_comp := by simp
  left_identity := by
    intros
    apply prod.hom_ext <;> simp [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  right_identity := by
    intros
    apply prod.hom_ext <;> simp [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  left_inverse := by
    intros
    apply prod.hom_ext <;> simp [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  right_inverse := by
    intros
    apply prod.hom_ext <;> simp [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  assoc := by
    intros
    apply prod.hom_ext <;> simp [pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The relation of a groupoid over a field has closed image as soon as that image is
locally closed. -/
private theorem isClosed_range_groupoid_relation
    {S : Scheme.{u}} {k : Type u} [Field k]
    (G : GroupoidScheme S)
    (hfield : G.objects.left = Spec (.of k))
    (h : IsLocallyClosed (Set.range (prod.lift G.target G.source).left.base)) :
    IsClosed (Set.range (prod.lift G.target G.source).left.base) := by
  let F : GroupoidScheme.Hom G (pairGroupoid G.objects) :=
    { mapObjects := 𝟙 _
      mapArrows := prod.lift G.target G.source
      map_source := by simp [pairGroupoid]
      map_target := by simp [pairGroupoid]
      map_identity := by
        apply prod.hom_ext <;>
          simp [pairGroupoid, G.target_identity, G.source_identity]
      map_comp := by
        intros
        dsimp only [pairGroupoid, GroupoidScheme.compose]
        apply prod.hom_ext <;>
          simp [G.target_comp, G.source_comp, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc] }
  exact isClosed_range_mapArrows_of_isLocallyClosed (k := k) F rfl hfield rfl h

/-- An immersed equivalence relation on the spectrum of a field is a closed immersion. -/
private theorem isClosedImmersion_equivalenceRelation_over_field
    {S : Scheme.{u}} {k : Type u} [Field k] {R U : Over S}
    (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source]
    (hfield : U.left = Spec (.of k)) [IsImmersion j.left] :
    IsClosedImmersion j.left := by
  obtain ⟨G, hG, _⟩ := existsUnique_groupoidScheme_of_isEquivalenceRelation j
  rcases hG with ⟨hobj, harr, hsource, htarget⟩
  cases hobj
  cases harr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsource htarget
  have hj : prod.lift G.target G.source = j := by
    apply prod.hom_ext
    · simpa using htarget
    · simpa using hsource
  have hc : IsClosed (Set.range j.left.base) := by
    rw [← hj]
    apply isClosed_range_groupoid_relation G hfield
    rw [hj]
    exact IsImmersion.isLocallyClosed_range (f := j.left)
  exact (IsClosedImmersion.iff_isPreimmersion (f := j.left)).mpr ⟨inferInstance, hc⟩

/-! ### Monomorphisms into schemes étale over a field -/

/-- A monomorphism into a coproduct of spectra of fields is an open immersion. -/
private theorem isOpenImmersion_of_mono_to_coproduct_fields
    {ι : Type v} [Small.{u} ι] (k : ι → Type u) [∀ i, Field (k i)]
    {Y : Scheme.{u}} (f : Y ⟶ ∐ fun i ↦ Spec (.of (k i))) [Mono f] :
    IsOpenImmersion f := by
  obtain ⟨J, e, he⟩ := exists_iso_coproduct_spec_of_mono k f
  have : IsOpenImmersion (Sigma.desc
      (fun j : J ↦ Sigma.ι (fun i ↦ Spec (.of (k i))) j.1)) := by
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    change Disjoint _ _
    rw [Set.disjoint_left]
    rintro z ⟨a, rfl⟩ ⟨b, hab⟩
    have heq := (sigmaι_eq_iff (fun i ↦ Spec (.of (k i))) j.1 i.1 b a).mp hab
    exact hij (Subtype.ext (congrArg Sigma.fst heq).symm)
  rw [← he]
  infer_instance

/-- A monomorphism into a scheme étale over the spectrum of a field is an open
immersion. -/
@[sga "3 XI 3.10" "special case"]
private theorem isOpenImmersion_of_mono_to_etale_field
    {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ Spec (.of k)) [Mono f] [Etale g] :
    IsOpenImmersion f := by
  obtain ⟨I, K, hfield, halg, hfinite, hsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k g).mp inferInstance
  have : IsOpenImmersion (f ≫ e.hom) :=
    isOpenImmersion_of_mono_to_coproduct_fields K (f ≫ e.hom)
  exact IsOpenImmersion.of_comp f e.hom

/-! ### The product of two affine schemes -/

/-- The spectrum of a tensor product over `ℤ` is a binary product of the two spectra. -/
private noncomputable def tensorProductBinaryFanIsLimit
    (A B : Type u) [CommRing A] [CommRing B] :
    IsLimit (BinaryFan.mk
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft
        (R := ℤ) (S := ℤ) (A := A) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ℤ) (A := A) (B := B)).toRingHom))) := by
  let c := CommRingCat.coproductCocone (.of A) (.of B)
  let hc := CommRingCat.coproductCoconeIsColimit (.of A) (.of B)
  let h : IsLimit (BinaryFan.mk c.inl.op c.inr.op) := BinaryCofan.IsColimit.op hc
  exact isLimitMapConeBinaryFanEquiv Scheme.Spec _ _ (isLimitOfPreserves Scheme.Spec h)

/-- The spectrum of a tensor product over `ℤ` as the product of the two spectra. -/
private noncomputable def tensorProductIsoProd
    (A B : Type u) [CommRing A] [CommRing B] :
    Spec (.of (A ⊗[ℤ] B)) ≅ Spec (.of A) ⨯ Spec (.of B) :=
  (tensorProductBinaryFanIsLimit A B).conePointUniqueUpToIso
    (t := BinaryFan.mk prod.fst prod.snd) (prodIsProd _ _)

private lemma tensorProductIsoProd_hom
    (A B : Type u) [CommRing A] [CommRing B] :
    (tensorProductIsoProd A B).hom = prod.lift
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft
        (R := ℤ) (S := ℤ) (A := A) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ℤ) (A := A) (B := B)).toRingHom)) := by
  apply prod.hom_ext
  · simp only [prod.lift_fst]
    exact (tensorProductBinaryFanIsLimit A B).conePointUniqueUpToIso_hom_comp
      (prodIsProd _ _) ⟨WalkingPair.left⟩
  · simp only [prod.lift_snd]
    exact (tensorProductBinaryFanIsLimit A B).conePointUniqueUpToIso_hom_comp
      (prodIsProd _ _) ⟨WalkingPair.right⟩

/-! ### Finiteness of the index set of a relation -/

/-- Under an inducing map, the closure of the image of the complement of an open set is
disjoint from the image of that open set. -/
private theorem closure_image_compl_disjoint_image_of_isInducing
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Topology.IsInducing f) {D : Set α} (hD : IsOpen D) :
    Disjoint (closure (f '' Dᶜ)) (f '' D) := by
  obtain ⟨V, hV, hVD⟩ := hf.isOpen_iff.mp hD
  rw [Set.disjoint_left]
  rintro _ hc ⟨x, hx, rfl⟩
  have hxV : f x ∈ V := by
    rwa [← Set.mem_preimage, hVD]
  obtain ⟨_, hyV, y, hy, rfl⟩ := (mem_closure_iff.mp hc) V hV hxV
  apply hy
  rwa [← hVD]

/-- A monomorphism from the spectrum of a field to an affine scheme is the spectrum of the
residue field at a prime of the target. -/
private theorem exists_residueFieldIso_of_mono
    {A K : Type u} [CommRing A] [Field K]
    (a : Spec (.of K) ⟶ Spec (.of A)) [Mono a] :
    ∃ (p : PrimeSpectrum A) (e : p.asIdeal.ResidueField ≃+* K),
      e.toRingHom.comp (algebraMap A p.asIdeal.ResidueField) = (Spec.preimage a).hom := by
  let f := (Spec.preimage a).hom
  have : Epi (CommRingCat.ofHom f) := ⟨by
    intro Z g h hgh
    apply Spec.map_injective
    apply (cancel_mono a).mp
    simpa [Spec.map_comp, f] using congrArg Spec.map hgh⟩
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hunit : p.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) :=
    fun _ hr ↦ isUnit_iff_ne_zero.mpr hr
  let j : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal f le_rfl hunit
  have hj : j.comp (algebraMap A p.asIdeal.ResidueField) = f := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p.asIdeal f le_rfl hunit r
  have : Epi (CommRingCat.ofHom j) :=
    epi_of_epi_fac (show CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField) ≫
      CommRingCat.ofHom j = CommRingCat.ofHom f from CommRingCat.hom_ext hj)
  let := j.toAlgebra
  have : Algebra.IsEpi p.asIdeal.ResidueField K := CommRingCat.epi_iff_epi.mp inferInstance
  exact ⟨p, RingEquiv.ofBijective j ⟨j.injective,
    Algebra.IsEpi.surjective_algebraMap_of_field⟩, hj⟩

/-- An injective family of primes whose off-diagonal residue-field products stay away from
the diagonal in their closure is finite: an infinite one would meet the diagonal, by
Stacks 088I. -/
private lemma finite_of_disjoint_offDiagonalClosure
    {A : Type u} [CommRing A] {k : Type v} [Field k]
    {ι : Type w} (p : ι → PrimeSpectrum A)
    [∀ i, Algebra k (p i).asIdeal.ResidueField]
    (hp : Function.Injective p)
    (hdisj : Disjoint
      (closure (⋃ i, ⋃ j, ⋃ (_ : i ≠ j),
        Set.range (PrimeSpectrum.comap
          (Space.Decent.residuePairMap A k p i j))))
      (Set.range (PrimeSpectrum.comap (Space.Decent.diagonalMap A)))) :
    Finite ι := by
  classical
  by_contra hfinite
  have : Infinite ι := not_finite_iff_infinite.mp hfinite
  let e : ℕ+ ↪ ι := (Function.Embedding.subtype _).trans (Infinite.natEmbedding ι)
  let p' : ℕ+ → PrimeSpectrum A := fun n => p (e n)
  let : ∀ n : ℕ+, Algebra k (p' n).asIdeal.ResidueField := fun n => inferInstance
  obtain ⟨z, hzC, hzD⟩ := Space.Decent.closure_iUnion_range_residuePairMap_meets_diagonal
    A k p' (hp.comp e.injective)
  have hsub :
      closure (⋃ n, ⋃ m, ⋃ (_ : n ≠ m),
        Set.range (PrimeSpectrum.comap
          (Space.Decent.residuePairMap A k p' n m))) ⊆
      closure (⋃ i, ⋃ j, ⋃ (_ : i ≠ j),
        Set.range (PrimeSpectrum.comap
          (Space.Decent.residuePairMap A k p i j))) := by
    apply closure_mono
    intro q hq
    simp only [Set.mem_iUnion] at hq ⊢
    obtain ⟨n, m, hnm, r, rfl⟩ := hq
    exact ⟨e n, e m, e.injective.ne hnm, r, rfl⟩
  exact (Set.disjoint_left.mp hdisj) (hsub hzC) hzD

/-! ### An étale morphism to a field with an immersed affine relation is finite -/

/-- A scheme étale over the spectrum of a field, monomorphic into an affine scheme carrying
an immersed relation with an open diagonal and a map from the self-intersection, is finite
over the field. -/
private theorem finite_etale_field_of_immersed_relation
    {A k : Type u} [CommRing A] [Field k] {T R : Scheme.{u}}
    (a : T ⟶ Spec (.of A)) [Mono a]
    (g : T ⟶ Spec (.of k)) [Etale g]
    (s t : R ⟶ Spec (.of A)) [IsImmersion (prod.lift s t)]
    (e : Spec (.of A) ⟶ R) [IsOpenImmersion e]
    (hes : e ≫ s = 𝟙 _) (het : e ≫ t = 𝟙 _)
    (c : pullback g g ⟶ R)
    (hcs : c ≫ s = pullback.fst g g ≫ a)
    (hct : c ≫ t = pullback.snd g g ≫ a) :
    IsFinite g := by
  classical
  obtain ⟨I, K, _, _, hfinite, _, E, hE⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k g).mp inferInstance
  let v (i : I) := Sigma.ι (fun i ↦ Spec (.of (K i))) i ≫ E.inv
  have hvg (i : I) : v i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k (K i))) := by
    rw [← hE]
    simp [v]
  have hvmono (i : I) : Mono (v i ≫ a) := by
    dsimp [v]
    infer_instance
  choose p ε hε using fun i ↦ exists_residueFieldIso_of_mono (v i ≫ a)
  let (i : I) : Algebra k (p i).asIdeal.ResidueField :=
    ((ε i).symm.toRingHom.comp (algebraMap k (K i))).toAlgebra
  let d (i : I) : Spec (.of (p i).asIdeal.ResidueField) ⟶ T :=
    Spec.map (CommRingCat.ofHom (ε i).symm.toRingHom) ≫ v i
  have hda (i : I) : d i ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap A (p i).asIdeal.ResidueField)) := by
    dsimp only [d]
    rw [Category.assoc, ← Spec.map_preimage (v i ≫ a), ← Spec.map_comp]
    congr 1
    ext r
    change (ε i).symm ((Spec.preimage (v i ≫ a)).hom r) = _
    rw [← hε i]
    exact (ε i).symm_apply_apply _
  have hdg (i : I) : d i ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap k (p i).asIdeal.ResidueField)) := by
    dsimp only [d]
    rw [Category.assoc, hvg, ← Spec.map_comp]
    rfl
  have hdap (i : I) (z : Spec (.of (p i).asIdeal.ResidueField)) : a (d i z) = p i := by
    rw [← Scheme.Hom.comp_apply, hda]
    exact Set.mem_singleton_iff.mp ((PrimeSpectrum.residueField_comap (p i)).le ⟨z, rfl⟩)
  have hpinj : Function.Injective p := by
    intro i j hij
    let zi := IsLocalRing.closedPoint (p i).asIdeal.ResidueField
    let zj := IsLocalRing.closedPoint (p j).asIdeal.ResidueField
    have hdE (m : I) : d m ≫ E.hom = Spec.map (CommRingCat.ofHom
        (ε m).symm.toRingHom) ≫ Sigma.ι (fun i ↦ Spec (.of (K i))) m := by
      simp [d, v]
    have hh : (d i ≫ E.hom) zi = (d j ≫ E.hom) zj :=
      congrArg E.hom (a.injective ((hdap i zi).trans (hij.trans (hdap j zj).symm)))
    rw [hdE, hdE] at hh
    exact congrArg Sigma.fst ((sigmaι_eq_iff _ i j _ _).mp hh)
  let j : R ⟶ Spec (.of (A ⊗[ℤ] A)) := prod.lift s t ≫ (tensorProductIsoProd A A).inv
  have : IsImmersion j := by
    dsimp [j]
    infer_instance
  have hj : j ≫ (tensorProductIsoProd A A).hom = prod.lift s t := by simp [j]
  have hed : e ≫ j = Spec.map (CommRingCat.ofHom (Space.Decent.diagonalMap A)) := by
    apply (cancel_mono (tensorProductIsoProd A A).hom).mp
    rw [Category.assoc, hj, tensorProductIsoProd_hom]
    apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst,
      prod.lift_snd, hes, het, ← Spec.map_comp]
    all_goals
      rw [← Spec.map_id]
      congr 1
      ext x
      simp [Space.Decent.diagonalMap]
  have hdisj := closure_image_compl_disjoint_image_of_isInducing
    j.isEmbedding.isInducing e.isOpenEmbedding.isOpen_range
  have hrange : j '' Set.range e = Set.range
      (PrimeSpectrum.comap (Space.Decent.diagonalMap A)) := by
    rw [← Set.range_comp]
    change Set.range (e ≫ j) = _
    rw [hed]
    rfl
  rw [hrange] at hdisj
  have hsub : (⋃ i, ⋃ l, ⋃ (_ : i ≠ l),
      Set.range (PrimeSpectrum.comap (Space.Decent.residuePairMap A k p i l))) ⊆
      j '' (Set.range e)ᶜ := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨i, l, hil, w, rfl⟩ := hz
    let L := (p i).asIdeal.ResidueField
    let M := (p l).asIdeal.ResidueField
    let b₁ : Spec (.of (L ⊗[k] M)) ⟶ Spec (.of L) :=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := k)
        (S := k) (A := L) (B := M)).toRingHom)
    let b₂ : Spec (.of (L ⊗[k] M)) ⟶ Spec (.of M) :=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := k) (A := L) (B := M)).toRingHom)
    have hb : b₁ ≫ d i ≫ g = b₂ ≫ d l ≫ g := by
      rw [hdg, hdg]
      change b₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        b₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k M))
      simp only [b₁, b₂, ← Spec.map_comp]
      congr 1
      ext r
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
    let b : Spec (.of (L ⊗[k] M)) ⟶ R :=
      pullback.lift (b₁ ≫ d i) (b₂ ≫ d l) (by simpa only [Category.assoc] using hb) ≫ c
    have hbs : b ≫ s = b₁ ≫ d i ≫ a := by
      simp [b, Category.assoc, hcs, pullback.lift_fst_assoc]
    have hbt : b ≫ t = b₂ ≫ d l ≫ a := by
      simp [b, Category.assoc, hct, pullback.lift_snd_assoc]
    have hbj : b ≫ j = Spec.map
        (CommRingCat.ofHom (Space.Decent.residuePairMap A k p i l)) := by
      apply (cancel_mono (tensorProductIsoProd A A).hom).mp
      rw [Category.assoc, hj, tensorProductIsoProd_hom]
      let : Algebra ℤ (L ⊗[k] M) := Ring.toIntAlgebra _
      let φ₁ := ((Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := L)
        (B := M)).toRingHom.comp (algebraMap A L)).toIntAlgHom
      let φ₂ := ((Algebra.TensorProduct.includeRight (R := k) (A := L)
        (B := M)).toRingHom.comp (algebraMap A M)).toIntAlgHom
      apply prod.hom_ext <;>
        simp only [Category.assoc, prod.lift_fst, prod.lift_snd, hbs, hbt, hda, b₁, b₂,
          ← Spec.map_comp] <;>
        congr 1 <;> ext x
      · exact (Algebra.TensorProduct.productMap_left_apply φ₁ φ₂ x).symm
      · exact (Algebra.TensorProduct.productMap_right_apply φ₁ φ₂ x).symm
    dsimp only [L, M] at b b₁ b₂
    let w' : Spec (.of ((p i).asIdeal.ResidueField ⊗[k]
        (p l).asIdeal.ResidueField)) :=
      OrderDual.ofDual (primeSpectrumOrderIsoSpec _ w)
    refine ⟨b w', ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hs : s (b w') = p i := by
        rw [← Scheme.Hom.comp_apply, hbs]
        exact hdap i (b₁ w')
      have ht : t (b w') = p l := by
        rw [← Scheme.Hom.comp_apply, hbt]
        exact hdap l (b₂ w')
      exact hil (hpinj (hs.symm.trans ((congrArg s hy).symm.trans
        ((congrArg (fun f : Spec (.of A) ⟶ Spec (.of A) ↦ f y) (hes.trans het.symm)).trans
          ((congrArg t hy).trans ht)))))
    · rw [← Scheme.Hom.comp_apply, hbj]
      rfl
  have : Finite I := finite_of_disjoint_offDiagonalClosure (k := k) p hpinj
    (hdisj.mono_left (closure_mono hsub))
  have (i : I) : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr (hfinite i)
  have : IsFinite (Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap k (K i))))) := isFinite_sigmaDesc
  rw [← hE]
  infer_instance

/-- An immersed relation on the base of a morphism in the over-category gives an immersed
relation on the underlying schemes. -/
private theorem isImmersion_prod_lift_of_relative
    {S : Scheme.{u}} {R U : Over S} (s t : R ⟶ U)
    [IsImmersion (prod.lift s t).left] :
    IsImmersion (prod.lift s.left t.left) := by
  let q := prod.lift (pullback.fst U.hom U.hom) (pullback.snd U.hom U.hom)
  have : IsImmersion q := MorphismProperty.of_isPullback
    (isPullback_diagonal_of_kernelPair (IsPullback.of_hasPullback U.hom U.hom))
    (inferInstance : IsImmersion (diag S))
  have heq : (prod.lift s t).left ≫ (Over.prodLeftIsoPullback U U).hom ≫ q =
      prod.lift s.left t.left := by
    apply prod.hom_ext <;> simp [q, ← Over.comp_left]
  rw [← heq]
  infer_instance

/-- The affine form of the finiteness criterion: the ambient scheme need only be affine, not
a spectrum presented as such. -/
private theorem finite_etale_field_of_immersed_affine_relation
    {k : Type u} [Field k] {U T R : Scheme.{u}} [IsAffine U]
    (a : T ⟶ U) [Mono a] (g : T ⟶ Spec (.of k)) [Etale g]
    (s t : R ⟶ U) [IsImmersion (prod.lift s t)]
    (e : U ⟶ R) [IsOpenImmersion e]
    (hes : e ≫ s = 𝟙 _) (het : e ≫ t = 𝟙 _)
    (c : pullback g g ⟶ R)
    (hcs : c ≫ s = pullback.fst g g ≫ a)
    (hct : c ≫ t = pullback.snd g g ≫ a) : IsFinite g := by
  let E := U.isoSpec
  have hprod : prod.lift s t ≫ prod.map E.hom E.hom =
      prod.lift (s ≫ E.hom) (t ≫ E.hom) := by ext <;> simp
  have : IsImmersion (prod.lift (s ≫ E.hom) (t ≫ E.hom)) := by
    rw [← hprod]
    infer_instance
  exact finite_etale_field_of_immersed_relation (a ≫ E.hom) g
    (s ≫ E.hom) (t ≫ E.hom) (E.inv ≫ e)
    (by simpa only [Category.assoc, Category.id_comp, E.inv_hom_id] using
      congrArg (fun h ↦ E.inv ≫ h ≫ E.hom) hes)
    (by simpa only [Category.assoc, Category.id_comp, E.inv_hom_id] using
      congrArg (fun h ↦ E.inv ≫ h ≫ E.hom) het) c
    (by simp [← Category.assoc, hcs]) (by simp [← Category.assoc, hct])

namespace Space

/-! ### Products in the big fppf category over a scheme -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site (instance search times out without
this shortcut). -/
private instance (priority := high) hasLimitsOfShape_discrete_presheaf_locallySeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_locallySeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_locallySeparated
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Site

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relation of a chart of a locally separated algebraic space -/

/-- On a locally separated algebraic space, a represented kernel pair of a chart is an
immersion into the product of the chart with itself. -/
private theorem isImmersion_of_represented_kernelPair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsep : IsLocallySeparatedOver B S hS X)
    {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    _root_.AlgebraicGeometry.IsImmersion (prod.lift ((Over.post B.inclusion).map s)
      ((Over.post B.inclusion).map t)).left := by
  let H := Over.post B.inclusion (X := B.obj hS)
  let Q := BigFppfOver.toScheme B S hS
  let j := prod.lift s t
  let e := asIso (prodComparison yoneda U U)
  let b := e.hom ≫ prod.map f f
  have hj : yoneda.map j ≫ e.hom = prod.lift (yoneda.map s) (yoneda.map t) := by
    apply prod.hom_ext <;>
      simp [e, j, prodComparison_fst, prodComparison_snd, ← yoneda.map_comp]
  have hpb : IsPullback (yoneda.map s ≫ f) (yoneda.map j) (diag X) b := by
    apply (isPullback_diagonal_of_kernelPair hR).of_iso
      (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    · simp
    · simpa using (Iso.comp_inv_eq e).mpr hj.symm
    · simp
    · simp [b]
  have : _root_.AlgebraicGeometry.IsImmersion (Q.map j) := hsep.property b _ j hpb
  let d := asIso (prodComparison H U U)
  have heq : Q.map j ≫ d.hom.left =
      (prod.lift (H.map s) (H.map t)).left := by
    change (H.map j ≫ d.hom).left = _
    congr 1
    apply prod.hom_ext <;>
      simp [d, j, prodComparison_fst, prodComparison_snd, ← H.map_comp]
  have : IsIso d.hom.left := by
    change IsIso ((Over.forget S).map d.hom)
    infer_instance
  have : _root_.AlgebraicGeometry.IsOpenImmersion d.hom.left :=
    IsOpenImmersion.of_isIso _
  have : _root_.AlgebraicGeometry.IsImmersion d.hom.left := inferInstance
  rw [← heq]
  exact @_root_.AlgebraicGeometry.IsImmersion.comp _ _ _ (Q.map j) d.hom.left
    ‹_root_.AlgebraicGeometry.IsImmersion (Q.map j)›
    ‹_root_.AlgebraicGeometry.IsImmersion d.hom.left›

/-- Contrapositive form of `isImmersion_of_represented_kernelPair`: if a represented kernel
pair of a chart fails to be an immersion into the product of the chart with itself, the
presheaf is not locally separated. This is the criterion used, e.g., to show that **Stacks
02Z1**'s quotient of the affine line is not locally separated. -/
theorem not_isLocallySeparatedOver_of_not_isImmersion_kernelPair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hnotimm : ¬ _root_.AlgebraicGeometry.IsImmersion (prod.lift ((Over.post B.inclusion).map s)
      ((Over.post B.inclusion).map t)).left) :
    ¬ IsLocallySeparatedOver B S hS X := fun hsep =>
  hnotimm (isImmersion_of_represented_kernelPair B S hS hsep f s t hR)

/-- On a locally separated algebraic space, the represented kernel pair of a field-valued
chart is affine: it is a closed subscheme of the product of two field spectra. -/
private theorem isAffine_represented_field_relation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsep : IsLocallySeparatedOver B S hS X)
    {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    {k : Type u} [Field k]
    (hfield : (BigFppfOver.toScheme B S hS).obj U = Spec (.of k)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj R) := by
  let H := Over.post B.inclusion (X := B.obj hS)
  let U' := H.obj U
  let j : PreRelation (H.obj R) U' := prod.lift (H.map s) (H.map t)
  have : IsEquivalenceRelation j.target j.source := by
    have ht : j.target = H.map s := by simp [PreRelation.target, j]
    have hs : j.source = H.map t := by simp [PreRelation.source, j]
    rw [ht, hs]
    exact isEquivalenceRelation_of_isPullback B S hS f s t hR
  have : _root_.AlgebraicGeometry.IsImmersion j.left :=
    isImmersion_of_represented_kernelPair B S hS hsep f s t hR
  have hfield' : U'.left = Spec (.of k) := hfield
  have : _root_.AlgebraicGeometry.IsClosedImmersion j.left :=
    isClosedImmersion_equivalenceRelation_over_field j hfield'
  have : _root_.AlgebraicGeometry.IsAffineHom j.left := inferInstance
  have : IsAffine U'.left := hfield'.symm ▸ inferInstance
  have : Subsingleton U'.left := hfield'.symm ▸ inferInstance
  have : _root_.AlgebraicGeometry.IsAffineHom U'.hom :=
    ⟨fun _ _ => IsAffineOpen.of_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)⟩
  have : IsAffine (pullback U'.hom U'.hom) := inferInstance
  have : IsAffine (U' ⨯ U').left :=
    isAffine_of_isAffineHom (Over.prodLeftIsoPullback U' U').hom
  exact @isAffine_of_isAffineHom _ _ j.left
    ‹_root_.AlgebraicGeometry.IsAffineHom j.left› ‹IsAffine (U' ⨯ U').left›

/-- The projection of the kernel pair of a field-valued point of an étale chart is étale:
it factors as an open immersion followed by an étale morphism. -/
private theorem etale_projection_of_kernelPair_over_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U V : BigFppfOver B S hS}
    (g : U ⟶ V) (φ : yoneda.obj V ⟶ X)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t)
      (yoneda.map g ≫ φ) (yoneda.map g ≫ φ))
    {k : Type u} [Field k]
    (hfield : (BigFppfOver.toScheme B S hS).obj U = Spec (.of k))
    [Mono ((BigFppfOver.toScheme B S hS).map g)] :
    Etale ((BigFppfOver.toScheme B S hS).map s) := by
  let Q := BigFppfOver.toScheme B S hS
  let f := yoneda.map g ≫ φ
  let M := hφ.rep.pullback f
  let a : M ⟶ V := yoneda.preimage (hφ.rep.fst f)
  let b : M ⟶ U := hφ.rep.snd f
  have hM : IsPullback (yoneda.map a) (yoneda.map b) φ f := by
    simpa [a, b] using hφ.rep.isPullback f
  let r' := hM.lift (yoneda.map t ≫ yoneda.map g) (yoneda.map s)
    (by simpa [Category.assoc, f] using hR.w.symm)
  let r : R ⟶ M := yoneda.preimage r'
  have hr : yoneda.map r = r' := yoneda.map_preimage r'
  have htop : IsPullback (yoneda.map t) (yoneda.map r)
      (yoneda.map g) (yoneda.map a) := by
    simpa only [hr, r'] using hR.flip.of_bot' hM
  have hscheme := (htop.of_map_of_faithful yoneda).map Q
  have : Mono (Q.map r) :=
    PullbackCone.mono_fst_of_is_pullback_of_mono hscheme.flip.isLimit
  have : Etale (Q.map b) := hφ.property f _ b hM
  have : Etale (Q.map b ≫ eqToHom hfield) := inferInstance
  have : _root_.AlgebraicGeometry.IsOpenImmersion (Q.map r) :=
    isOpenImmersion_of_mono_to_etale_field (Q.map r) (Q.map b ≫ eqToHom hfield)
  have hcomp : r ≫ b = s := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hr]
    exact hM.lift_snd _ _ _
  rw [← hcomp, Q.map_comp]
  infer_instance

/-- Every field-valued point of a representable presheaf is equivalent to one presented by a
monomorphism, namely the residue-field point at the scheme point it selects. -/
private theorem exists_monomorphic_chart_representative
    (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    ∃ q : FieldValuedPoint B S hS (yoneda.obj U),
      q.class B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U) ∧
      Mono ((BigFppfOver.toScheme B S hS).map q.value) := by
  let Q := BigFppfOver.toScheme B S hS
  let T := Q.obj U
  let pAbs : _root_.AlgebraicGeometry.FieldValuedPoint T :=
    { carrier := p.carrier
      field := p.field
      map := Q.map p.value }
  let z := pAbs.point
  have : _root_.AlgebraicGeometry.IsAffineHom (T.fromSpecResidueField z) :=
    ⟨fun _ _ => IsAffineOpen.of_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)⟩
  have hK : B.Contains (Spec (T.residueField z)) :=
    (Scheme.size_le_of_mono_quasiCompact (T.fromSpecResidueField z)).trans_lt U.left.2
  let kobj := B.obj hK
  let i : kobj ⟶ U.left := B.inclusion.preimage (T.fromSpecResidueField z)
  let q : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := T.residueField z
      contained := hK
      toBase := B.inclusion.map (i ≫ U.hom)
      value := (show Over.mk (i ≫ U.hom) ⟶ U from Over.homMk i) }
  have hq : Q.map q.value = T.fromSpecResidueField z := B.inclusion.map_preimage _
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨φ, hφ, _⟩ :=
      (_root_.AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest z) pAbs
      (Scheme.fromSpecResidueField_apply z _).symm
    let φ' : B.inclusion.obj p.siteObject.left ⟶ B.inclusion.obj q.siteObject.left := φ
    let r := B.inclusion.preimage φ'
    have hr : r ≫ q.value.left = p.value.left := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      change φ' ≫ Q.map q.value = Q.map p.value
      rwa [hq]
    let a : p.siteObject ⟶ q.siteObject := Over.homMk r (by
      calc
        r ≫ q.siteObject.hom = r ≫ (q.value.left ≫ U.hom) :=
          congrArg (fun a ↦ r ≫ a) q.value.w.symm
        _ = p.value.left ≫ U.hom := by rw [← Category.assoc, hr]
        _ = p.siteObject.hom := p.value.w)
    exact (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
      (p := p) (q := q)
      ⟨p, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p,
        ⟨a, Over.OverMorphism.ext hr⟩⟩).symm
  · rw [hq]
    infer_instance

/-- A property of schemes stable under base change, verified on a represented morphism,
transfers to any morphism of presheaves isomorphic to it as an arrow. -/
private theorem presheaf_of_represented_arrowIso
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {R U : BigFppfOver B S hS}
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : R ⟶ U) (g : Y ⟶ Z)
    (e : Arrow.mk (yoneda.map s) ≅ Arrow.mk g)
    (hs : P ((BigFppfOver.toScheme B S hS).map s)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g := by
  let Q := BigFppfOver.toScheme B S hS
  let P' := P.inverseImage Q
  have : P'.IsStableUnderBaseChange := by
    constructor
    intro W Y Z T f' g f g' h hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (h.map Q) hf
  exact (P'.presheaf.arrow_mk_iso_iff e).mp (MorphismProperty.relative_map hs)

end Site

/-! ### Points of a locally separated algebraic space -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of a monomorphic field-valued point of an étale chart of a locally separated
algebraic space satisfies condition (3) of Stacks 03JU. -/
private theorem hasEtaleQuasiCompactFieldRepresentative_of_chart
    (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsLocallySeparatedOver B S hS X)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    [Mono ((BigFppfOver.toScheme B S hS).map p.value)] :
    HasEtaleQuasiCompactFieldRepresentative B S hS X
      (pointsMap B S hS (yoneda.obj U) φ (p.class B S hS (yoneda.obj U))) := by
  let Q := BigFppfOver.toScheme B S hS
  let q := FieldValuedPoint.map B S hS (yoneda.obj U) φ p
  let f := yoneda.map p.value ≫ φ
  have hf : fieldMorphism B S hS X q = f := by
    apply yonedaEquiv.injective
    simp only [fieldMorphism, Equiv.apply_symm_apply]
    rfl
  let rep := hX.diagonal_representable.of_diag f
  let R := rep.pullback f
  let s : R ⟶ p.siteObject := rep.fst' f
  let t : R ⟶ p.siteObject := rep.snd f
  have hR : IsPullback (yoneda.map s) (yoneda.map t) f f := rep.isPullback' f
  have : IsAffine (Q.obj R) :=
    isAffine_represented_field_relation B S hS hsep f s t hR (k := p.carrier) rfl
  have : IsAffine (Q.obj p.siteObject) := inferInstanceAs (IsAffine (Spec (.of p.carrier)))
  have : Etale (Q.map s) :=
    etale_projection_of_kernelPair_over_chart B S hS p.value φ hφ s t hR
      (k := p.carrier) rfl
  have : Etale (Q.map t) :=
    etale_projection_of_kernelPair_over_chart B S hS p.value φ hφ t s hR.flip
      (k := p.carrier) rfl
  refine ⟨q, rfl, ?_⟩
  have hRq : IsPullback (yoneda.map s) (yoneda.map t)
      (fieldMorphism B S hS X q) (fieldMorphism B S hS X q) := by
    simpa only [hf] using hR
  let P : MorphismProperty Scheme.{u} := @Etale.{u} ⊓ @QuasiCompact.{u}
  have : MorphismProperty.IsStableUnderBaseChange P :=
    @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _
      Etale.etale_isStableUnderBaseChange quasiCompact_isStableUnderBaseChange
  let g := fieldMorphism B S hS X q
  let e₁ : Arrow.mk (yoneda.map s) ≅ Arrow.mk (pullback.fst g g) :=
    Arrow.isoMk' (yoneda.map s) (pullback.fst g g) hRq.isoPullback (Iso.refl _) (by
      simp only [Iso.refl_hom]
      exact hRq.isoPullback_hom_fst)
  let e₂ : Arrow.mk (yoneda.map t) ≅ Arrow.mk (pullback.snd g g) :=
    Arrow.isoMk' (yoneda.map t) (pullback.snd g g) hRq.isoPullback (Iso.refl _) (by
      simp only [Iso.refl_hom]
      exact hRq.isoPullback_hom_snd)
  exact ⟨presheaf_of_represented_arrowIso B S hS P
      s _ e₁ ⟨inferInstance, inferInstance⟩,
    presheaf_of_represented_arrowIso B S hS P
      t _ e₂ ⟨inferInstance, inferInstance⟩⟩

/-- **Stacks 03JU, condition (3), on a locally separated algebraic space.** Every point of an
algebraic space which is locally separated over its base scheme has a field-valued
representative whose two self-intersection projections are étale and quasi-compact. -/
theorem hasEtaleQuasiCompactFieldRepresentative_of_isLocallySeparatedOver
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsLocallySeparatedOver B S hS X)
    (x : points B S hS X) :
    HasEtaleQuasiCompactFieldRepresentative B S hS X x := by
  classical
  obtain ⟨U, φ, hsurj, hEtale⟩ := hX.exists_atlas
  obtain ⟨uClass, huClass⟩ :=
    ((surjective_iff_surjective_pointsMap B S hS X hX U φ).mp hsurj) x
  obtain ⟨u, rfl⟩ := Quot.exists_rep uClass
  obtain ⟨q, hq, hqmono⟩ := exists_monomorphic_chart_representative B S hS U u
  have hrep := hasEtaleQuasiCompactFieldRepresentative_of_chart B S hS hX hsep U φ hEtale q
  rwa [hq, huClass] at hrep

/-- An algebraic space which is locally separated over its base scheme has property `(β)` of
Stacks 03JX: condition (1) of Stacks 03JU holds at every one of its points. -/
theorem hasFiniteRelationFibersAtEveryPoint_of_isLocallySeparatedOver
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsLocallySeparatedOver B S hS X) :
    HasFiniteRelationFibersAtEveryPoint B S hS X := fun x ↦
  (hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS X hX x).mpr
    ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
        B S hS X hX x).mpr
      (hasEtaleQuasiCompactFieldRepresentative_of_isLocallySeparatedOver B S hS hX hsep x))

/-- On an algebraic space which is locally separated over its base scheme, a cartesian square
exhibiting an object `W` of the site as the fibre product of an étale chart by an affine
scheme with a monomorphism from the spectrum of a field has its projection to that field
spectrum a finite morphism. -/
theorem isFinite_of_isPullback_fieldMorphism_of_isLocallySeparatedOver
    (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsLocallySeparatedOver B S hS X)
    (p : FieldValuedPoint B S hS X)
    [Mono (fieldMorphism B S hS X p)]
    (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    {W : BigFppfOver B S hS} (a : W ⟶ V) (g : W ⟶ p.siteObject)
    (hF : IsPullback (yoneda.map a) (yoneda.map g) ψ (fieldMorphism B S hS X p)) :
    _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) := by
  let Q := BigFppfOver.toScheme B S hS
  let H := Over.post B.inclusion (X := B.obj hS)
  let f := fieldMorphism B S hS X p
  have : Mono (yoneda.map a) := PullbackCone.mono_fst_of_is_pullback_of_mono hF.isLimit
  have : Mono a := yoneda.mono_of_mono_map inferInstance
  have : Mono (Q.map a) := inferInstance
  have : Etale (Q.map g) := hψ.property f _ g hF
  let rep := hX.diagonal_representable.of_diag ψ
  let R := rep.pullback ψ
  let s : R ⟶ V := rep.fst' ψ
  let t : R ⟶ V := rep.snd ψ
  have hR : IsPullback (yoneda.map s) (yoneda.map t) ψ ψ := rep.isPullback' ψ
  let e' := hR.lift (𝟙 _) (𝟙 _) (by simp)
  let e : V ⟶ R := yoneda.preimage e'
  have hes : e ≫ s = 𝟙 _ := by
    apply yoneda.map_injective
    simp [yoneda.map_comp, e, e']
  have het : e ≫ t = 𝟙 _ := by
    apply yoneda.map_injective
    simp [yoneda.map_comp, e, e']
  have hQes : Q.map e ≫ Q.map s = 𝟙 _ := by rw [← Q.map_comp, hes, Q.map_id]
  have : Etale (Q.map s) := hψ.property ψ _ s hR.flip
  have : Etale (Q.map e ≫ Q.map s) := by
    rw [hQes]
    infer_instance
  have : Etale (Q.map e) := Etale.of_comp (Q.map e) (Q.map s)
  have : Mono (Q.map e) := mono_of_mono_fac hQes
  have : _root_.AlgebraicGeometry.IsImmersion (prod.lift (H.map s) (H.map t)).left :=
    isImmersion_of_represented_kernelPair B S hS hsep ψ s t hR
  have : _root_.AlgebraicGeometry.IsImmersion (prod.lift (Q.map s) (Q.map t)) :=
    isImmersion_prod_lift_of_relative (H.map s) (H.map t)
  let D := pullback g g
  let l₁ : D ⟶ W := pullback.fst g g
  let l₂ : D ⟶ W := pullback.snd g g
  have hw : yoneda.map (l₁ ≫ a) ≫ ψ = yoneda.map (l₂ ≫ a) ≫ ψ := by
    simp only [yoneda.map_comp, Category.assoc]
    rw [hF.w]
    simp only [← Category.assoc, ← yoneda.map_comp]
    rw [show l₁ ≫ g = l₂ ≫ g from pullback.condition]
  let c' := hR.lift (yoneda.map (l₁ ≫ a)) (yoneda.map (l₂ ≫ a)) hw
  let c : D ⟶ R := yoneda.preimage c'
  have hcs : c ≫ s = l₁ ≫ a := by
    apply yoneda.map_injective
    simp [yoneda.map_comp, c, c']
  have hct : c ≫ t = l₂ ≫ a := by
    apply yoneda.map_injective
    simp [yoneda.map_comp, c, c']
  have hD : IsPullback (Q.map l₁) (Q.map l₂) (Q.map g) (Q.map g) :=
    (IsPullback.of_hasPullback g g).map Q
  let cQ : pullback (Q.map g) (Q.map g) ⟶ Q.obj R := hD.isoPullback.inv ≫ Q.map c
  have hcQs : cQ ≫ Q.map s = pullback.fst (Q.map g) (Q.map g) ≫ Q.map a := by
    dsimp only [cQ]
    rw [Category.assoc, ← Q.map_comp, hcs, Q.map_comp,
      ← Category.assoc, hD.isoPullback_inv_fst]
  have hcQt : cQ ≫ Q.map t = pullback.snd (Q.map g) (Q.map g) ≫ Q.map a := by
    dsimp only [cQ]
    rw [Category.assoc, ← Q.map_comp, hct, Q.map_comp,
      ← Category.assoc, hD.isoPullback_inv_snd]
  have : IsAffine (Q.obj V) := hV
  exact finite_etale_field_of_immersed_affine_relation
    (k := p.carrier) (Q.map a) (Q.map g) (Q.map s) (Q.map t) (Q.map e)
    hQes (by rw [← Q.map_comp, het, Q.map_id]) cQ hcQs hcQt

/-- On an algebraic space which is locally separated over its base scheme, the base change of
a monomorphism from the spectrum of a field along an étale chart by an affine scheme is a
finite morphism. -/
theorem isFinite_pullback_fieldMorphism_of_isLocallySeparatedOver
    (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsLocallySeparatedOver B S hS X)
    (p : FieldValuedPoint B S hS X)
    [Mono (fieldMorphism B S hS X p)]
    (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.fst (fieldMorphism B S hS X p) ψ) :=
  presheaf_of_represented_arrowIso B S hS
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (hψ.rep.snd (fieldMorphism B S hS X p))
    (pullback.fst (fieldMorphism B S hS X p) ψ)
    (Arrow.isoMk (hψ.rep.isPullback' (fieldMorphism B S hS X p)).flip.isoPullback
      (Iso.refl _) (by simp))
    (isFinite_of_isPullback_fieldMorphism_of_isLocallySeparatedOver B S hS hX hsep p V hV ψ hψ
      (hψ.rep.fst' (fieldMorphism B S hS X p)) (hψ.rep.snd (fieldMorphism B S hS X p))
      (hψ.rep.isPullback' (fieldMorphism B S hS X p)))

/-! ### Decency -/

/-- **Stacks 088J, over the base scheme.** An algebraic space which is locally separated over
its base scheme is decent: every one of its points is represented by a quasi-compact
monomorphism from the spectrum of a field.

The monomorphism comes from condition (3) of Stacks 03JU, which holds at every point by
`AlgebraicGeometry.Space.hasEtaleQuasiCompactFieldRepresentative_of_isLocallySeparatedOver`,
through the implication from condition (3) to condition (4) of that tag. It is quasi-compact
because its base change along every étale chart by an affine scheme is finite. -/
theorem isDecentSpace_of_isLocallySeparatedOver (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsLocallySeparatedOver B S hS X) :
    IsDecentSpace B S hS X := by
  intro x
  obtain ⟨p, hp, hmono⟩ :=
    hasMonomorphicFieldRepresentative_of_hasEtaleQuasiCompactFieldRepresentative B S hS hX x
      (hasEtaleQuasiCompactFieldRepresentative_of_isLocallySeparatedOver B S hS hX hsep x)
  exact ⟨p, hp, hmono, isQuasiCompact_fieldMorphism_of_isFinite_pullback B S hS hX p
    fun V hV ψ hψ _ a g sq ↦
      isFinite_of_isPullback_fieldMorphism_of_isLocallySeparatedOver B S hS hX hsep p V hV ψ
        hψ a g sq⟩

/-- **Stacks 088J.** A locally separated algebraic space is decent. -/
@[stacks 088J]
theorem isDecentSpace_of_isAbsolutelyLocallySeparated (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsAbsolutelyLocallySeparated B S hS hZ X) :
    IsDecentSpace B S hS X :=
  isDecentSpace_of_isLocallySeparatedOver B S hS hX
    (isLocallySeparatedOver_of_isAbsolutelyLocallySeparated B S hS hZ hX hsep)

end Main

end Space

end AlgebraicGeometry

-- Remark 03E0 observes that the conclusions available for decent algebraic spaces are also
-- available for a locally separated algebraic space, because such a space is decent; that
-- implication is Stacks 088J above.
add_to_stacks 03E0 "a locally separated algebraic space is decent"
  AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyLocallySeparated

end

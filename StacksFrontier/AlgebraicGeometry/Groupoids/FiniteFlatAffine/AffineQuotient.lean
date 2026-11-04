module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FppfLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Module.Free.Basis
import all StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient.FppfQuotient
import all StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient.LocalInvariants

/-!
# Finite flat equivalence relations on affine schemes

Let `G` be a groupoid scheme with affine object and arrow schemes whose source and target maps
are finite locally free, and suppose the pair `(target, source)` is an equivalence relation.
Then the spectrum of the ring of invariant functions is the quotient: the canonical morphism
from the object scheme is finite locally free, the arrow scheme is its kernel pair, the
structure morphism to the base descends along it, and the quotient represents the fppf
quotient sheaf of the relation.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.invariantSpectrumBaseMap`: the descent of the structure
  morphism of the object scheme along the quotient map.
* `AlgebraicGeometry.GroupoidScheme.invariantSpectrumOver` and
  `AlgebraicGeometry.GroupoidScheme.toInvariantSpectrumOver`: the quotient as a scheme over
  the base, and the canonical projection to it.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isFiniteLocallyFree_objectsToInvariantSpectrum`: the
  quotient map is finite locally free.
* `AlgebraicGeometry.GroupoidScheme.isPullback_objectsToInvariantSpectrum`: the arrow scheme
  is the kernel pair of the quotient map.
* `AlgebraicGeometry.GroupoidScheme.isIso_quotientSheafToInvariantSpectrum`: the quotient
  represents the fppf quotient sheaf.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Ring-theoretic preliminaries -/

/-- Over a local ring, the image of the maximal ideal under an integral ring map lies in the
Jacobson radical. -/
private alias map_maximalIdeal_le_jacobson :=
    AlgebraicGeometry.map_maximalIdeal_le_jacobson_of_local_integral

/-- If the fibres of a finite ring map over one maximal ideal already dominate every maximal
ideal of the source through a second map, then the source has finitely many maximal ideals. -/
private theorem finite_maximalSpectrum_of_orbit {A B : Type u} [CommRing A] [CommRing B]
    (t s : A →+* B) (hfinite : letI : Algebra A B := t.toAlgebra; Module.Finite A B)
    (htint : t.IsIntegral) (hsint : s.IsIntegral) (p₀ : MaximalSpectrum A)
    (horbit : ∀ p : MaximalSpectrum A, ∃ q : PrimeSpectrum B,
      PrimeSpectrum.comap t q = p₀.toPrimeSpectrum ∧
      PrimeSpectrum.comap s q = p.toPrimeSpectrum) :
    Finite (MaximalSpectrum A) := by
  let _ : Algebra A B := t.toAlgebra
  let _ : Module.Finite A B := hfinite
  have hF : {q : PrimeSpectrum B | PrimeSpectrum.comap t q = p₀.toPrimeSpectrum}.Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton p₀.toPrimeSpectrum
  let _ : Finite {q : PrimeSpectrum B | PrimeSpectrum.comap t q = p₀.toPrimeSpectrum} :=
    hF.to_subtype
  refine Finite.of_surjective
    (fun q : {q : PrimeSpectrum B | PrimeSpectrum.comap t q = p₀.toPrimeSpectrum} ↦
      (⟨(PrimeSpectrum.comap s q.1).asIdeal, ?_⟩ : MaximalSpectrum A)) ?_
  · have hqt : Ideal.comap t q.1.asIdeal = p₀.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal, MaximalSpectrum.toPrimeSpectrum] using
        congrArg PrimeSpectrum.asIdeal q.2
    have _ : q.1.asIdeal.IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' t htint q.1.asIdeal ?_
      rw [hqt]
      exact p₀.isMaximal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' s hsint q.1.asIdeal
  · intro p
    obtain ⟨q, hqt, hqs⟩ := horbit p
    exact ⟨⟨q, hqt⟩, MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal hqs)⟩

/-- Every local ring admits a flat local extension with infinite residue field. -/
private theorem exists_flat_localRing_infinite_residueField (R : Type u) [CommRing R]
    [IsLocalRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')) (_ : Module.Flat R R'),
      Infinite (IsLocalRing.ResidueField R') := by
  have _ : Infinite (Polynomial (IsLocalRing.ResidueField R)) :=
    Infinite.of_injective (fun n ↦ (Polynomial.X : Polynomial _) ^ n) fun m n h ↦ by
      simpa only [Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree h
  let _ : Infinite (RatFunc (IsLocalRing.ResidueField R)) :=
    Infinite.of_injective (algebraMap (Polynomial (IsLocalRing.ResidueField R)) _)
      (RatFunc.algebraMap_injective (IsLocalRing.ResidueField R))
  obtain ⟨R', hComm, hAlg, hLocal, hLocalHom, hflat, -, hres⟩ :=
    IsLocalRing.exists_flat_residueField_algEquiv R (RatFunc (IsLocalRing.ResidueField R))
  obtain ⟨e⟩ := hres
  exact ⟨R', hComm, hAlg, hLocal, hLocalHom, hflat,
    Infinite.of_injective e.symm e.symm.injective⟩

/-- If the canonical map out of the tensor square of an algebra is surjective, the image of
the second factor spans the target over the first. -/
private theorem span_range_eq_top_of_lift_surjective {C A B : Type u} [CommRing C] [CommRing A]
    [CommRing B] [Algebra C A] [Algebra C B] (f g : A →ₐ[C] B)
    (hfg : Function.Surjective
      (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _)) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    Submodule.span A (Set.range g) = ⊤ := by
  let _ : Algebra A B := f.toRingHom.toAlgebra
  have hmem (x : A ⊗[C] A) : Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) x ∈
      Submodule.span A (Set.range g) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    | tmul a a' =>
        rw [Algebra.TensorProduct.lift_tmul]
        have hg : g a' ∈ Submodule.span A (Set.range g) :=
          Submodule.subset_span (Set.mem_range_self a')
        show algebraMap A B a * g a' ∈ Submodule.span A (Set.range g)
        simpa [Algebra.smul_def] using Submodule.smul_mem _ a hg
  refine top_unique fun b _ ↦ ?_
  obtain ⟨x, rfl⟩ := hfg b
  exact hmem x

/-- The rank of a finite flat module at a maximal ideal is the dimension of its fibre. -/
private alias finrank_quotient_tensor_eq_rankAtStalk :=
    AlgebraicGeometry.finrank_quotient_tensor_eq_rankAtStalk

/-! ### Fibre ranks of an affine morphism -/

/-- The fibre rank of a finite flat morphism of affine schemes is the fibre rank of its map on
global functions. -/
private alias finrank_appTop := AlgebraicGeometry.finrank_appTop

/-- A finite basis of an algebra makes the corresponding morphism of spectra finite locally
free. -/
private theorem isFiniteLocallyFree_specMap_of_basis (R S : CommRingCat.{u}) (φ : R ⟶ S) {n : ℕ}
    (b : letI := φ.hom.toAlgebra; Module.Basis (Fin n) R S) :
    IsFiniteLocallyFree (Spec.map φ) := by
  let _ : Algebra R S := φ.hom.toAlgebra
  let _ : Module.Free R S := Module.Free.of_basis b
  let _ : Module.Finite R S := Module.Finite.of_basis b
  let _ : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  have hfin : φ.hom.Finite := Module.Finite.of_basis b
  have hflat : φ.hom.Flat := show Module.Flat R S from inferInstance
  have hfp : φ.hom.FinitePresentation :=
    show Algebra.FinitePresentation R S from
      (Module.FinitePresentation.iff_finitePresentation_of_finite (R := R) (S := S)).mp
        inferInstance
  rw [specMap_finiteLocallyFree_iff, IsFinite.SpecMap_iff, Flat.SpecMap_iff,
    LocallyOfFinitePresentation.SpecMap_iff]
  exact ⟨hfin, hflat, hfp⟩

/-! ### The arrow ring as a tensor square -/

/-- Two generalized points of the arrow scheme of an equivalence relation agree as soon as
they have the same source and the same target. -/
private alias arrows_hom_ext := AlgebraicGeometry.arrows_hom_ext

/-- The canonical map out of the tensor square restricts to the source map on the left factor. -/
private theorem lift_tmul_one_eq_sourceMap {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : Γ(G.objects.left, ⊤)) :
    letI := invariantRingAlgebraArrow G
    Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G) (fun _ _ ↦ Commute.all _ _)
      (a ⊗ₜ[invariantRing G] 1) = sourceMap G a := by
  let _ := invariantRingAlgebraArrow G
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- The canonical map out of the tensor square restricts to the target map on the right factor. -/
private theorem lift_one_tmul_eq_targetMap {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : Γ(G.objects.left, ⊤)) :
    letI := invariantRingAlgebraArrow G
    Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G) (fun _ _ ↦ Commute.all _ _)
      (1 ⊗ₜ[invariantRing G] a) = targetMap G a := by
  let _ := invariantRingAlgebraArrow G
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- For an equivalence relation with affine object and arrow schemes and finite locally free
source, the canonical map from the tensor square of the object ring over the invariant ring to
the arrow ring is surjective. -/
private theorem tensorMap_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source] :
    letI := invariantRingAlgebraArrow G
    Function.Surjective (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      fun _ _ ↦ Commute.all _ _) := by
  let _ := invariantRingAlgebraArrow G
  set k := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (sourceAlgHom G)
    (targetAlgHom G) fun _ _ ↦ Commute.all _ _).toRingHom) with hk
  let l := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
    Γ(G.objects.left, ⊤) →+* objectRingBaseChange G Γ(G.objects.left, ⊤)))
  let r := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
    Γ(G.objects.left, ⊤) →ₐ[invariantRing G] objectRingBaseChange G
      Γ(G.objects.left, ⊤)).toRingHom)
  have hl : k ≫ l = Spec.map G.source.left.appTop := by
    rw [hk, ← Spec.map_comp]
    congr 1
    ext a
    exact lift_tmul_one_eq_sourceMap G a
  have hr : k ≫ r = Spec.map G.target.left.appTop := by
    rw [hk, ← Spec.map_comp]
    congr 1
    ext a
    exact lift_one_tmul_eq_targetMap G a
  have key (m : _ ⟶ Spec (.of Γ(G.objects.left, ⊤))) (h : G.arrows.left ⟶ G.objects.left)
      (hm : k ≫ m = Spec.map h.appTop) :
      k ≫ m ≫ G.objects.left.isoSpec.inv = G.arrows.left.isoSpec.inv ≫ h := by
    have hs : G.arrows.left.isoSpec.hom ≫ k ≫ m = h ≫ G.objects.left.isoSpec.hom := by
      rw [hm]
      exact (Scheme.toSpecΓ_naturality h).symm
    rw [← cancel_epi G.arrows.left.isoSpec.hom]
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun a ↦ a ≫ G.objects.left.isoSpec.inv) hs
  let _ : Mono k := ⟨fun f g h ↦ by
    refine (cancel_mono G.arrows.left.isoSpec.inv).1 (arrows_hom_ext G _ _ ?_ ?_)
    · simpa only [Category.assoc, ← key r _ hr] using
        congrArg (fun a ↦ a ≫ r ≫ G.objects.left.isoSpec.inv) h
    · simpa only [Category.assoc, ← key l _ hl] using
        congrArg (fun a ↦ a ≫ l ≫ G.objects.left.isoSpec.inv) h⟩
  let _ : IsFinite G.source.left := IsFiniteLocallyFree.isFinite _
  let _ : IsFinite (k ≫ l) := by
    rw [hl, IsFinite.SpecMap_iff]
    exact G.source.left.finite_appTop
  let _ : IsFinite k := IsFinite.of_comp k l
  let _ : IsClosedImmersion k :=
    (IsClosedImmersion.iff_isFinite_and_mono k).mpr ⟨inferInstance, inferInstance⟩
  intro b
  obtain ⟨a, ha⟩ :=
    (Scheme.ΓSpecIso (.of Γ(G.arrows.left, ⊤))).commRingCatIsoToRingEquiv.surjective.comp
      (IsClosedImmersion.isAffine_surjective_of_isAffine k).2 b
  refine ⟨(Scheme.ΓSpecIso (.of (objectRingBaseChange G Γ(G.objects.left, ⊤)))).hom a, ?_⟩
  change (k.appTop ≫ (Scheme.ΓSpecIso (.of Γ(G.arrows.left, ⊤))).hom) a = b at ha
  rwa [Scheme.ΓSpecIso_naturality] at ha

/-- For an equivalence relation with finite locally free source, the fibre rank of the source
map is the same at the source and at the target of an arrow. -/
private theorem source_finrank_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsEquivalenceRelation G.target G.source]
    (r : G.arrows.left) :
    G.source.left.finrank (G.source.left.base r) =
      G.source.left.finrank (G.target.left.base r) := by
  let _ : IsFinite ((Over.forget S).map G.source) :=
    IsFiniteLocallyFree.isFinite G.source.left
  let _ : Flat ((Over.forget S).map G.source) := IsFiniteLocallyFree.flat G.source.left
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _
      ((G.comp_source_isPullback).map (Over.forget S)) r).symm.trans
    (Scheme.Hom.finrank_of_isPullback _ _ _ _
      ((IsPullback.of_hasPullback G.source G.target).map (Over.forget S)) r)

/-- Over a local invariant ring, every maximal ideal of the object ring has the same image in
the invariant spectrum. -/
private theorem objectsToInvariantSpectrum_base_eq_of_maximal {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsLocalRing (invariantRing G)] (p q : MaximalSpectrum Γ(G.objects.left, ⊤)) :
    (objectsToInvariantSpectrum G).base
        (G.objects.left.isoSpec.inv.base p.toPrimeSpectrum) =
      (objectsToInvariantSpectrum G).base
        (G.objects.left.isoSpec.inv.base q.toPrimeSpectrum) := by
  have hmax (p : MaximalSpectrum Γ(G.objects.left, ⊤)) :
      Ideal.comap (invariantRing G).subtype p.asIdeal =
        IsLocalRing.maximalIdeal (invariantRing G) := by
    let _ : p.asIdeal.IsMaximal := p.isMaximal
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _
      (isIntegral_invariantRing G) p.asIdeal)
  have he (p : PrimeSpectrum Γ(G.objects.left, ⊤)) :
      G.objects.left.isoSpec.hom.base (G.objects.left.isoSpec.inv.base p) = p :=
    congrArg (fun k : Spec (.of Γ(G.objects.left, ⊤)) ⟶ Spec (.of Γ(G.objects.left, ⊤)) ↦ k.base p)
      G.objects.left.isoSpec.inv_hom_id
  rw [objectsToInvariantSpectrum_base, objectsToInvariantSpectrum_base, he, he]
  exact PrimeSpectrum.ext ((hmax p).trans (hmax q).symm)

/-- Over a local invariant ring, the object ring of an equivalence relation is semilocal. -/
private alias finite_maximalSpectrum_objectRing :=
    AlgebraicGeometry.objectRing_finite_maximalSpectrum_of_local_invariants

/-! ### The quotient over a local invariant ring -/

/-- Over a local invariant ring with infinite residue field, the object ring of an equivalence
relation is finite free over the invariant ring and the arrow ring is its tensor square over
the invariant ring. -/
private theorem exists_basis_tensorEquiv_of_local_invariants {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] [IsLocalRing (invariantRing G)]
    [Infinite (IsLocalRing.ResidueField (invariantRing G))] :
    ∃ (n : ℕ) (_ : Module.Basis (Fin n) (invariantRing G) Γ(G.objects.left, ⊤))
      (e : Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤) ≃+*
        Γ(G.arrows.left, ⊤)),
      ∀ a a', e (a ⊗ₜ[invariantRing G] a') = sourceMap G a * targetMap G a' := by
  classical
  let _ : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
  let _ : IsFinite G.source.left := IsFiniteLocallyFree.isFinite _
  let _ : Flat G.source.left := IsFiniteLocallyFree.flat _
  let _ : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := G.source.left.finite_appTop
  let _ : Module.Flat Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := G.source.left.flat_appTop
  obtain ⟨r, hrank⟩ : ∃ r, ∀ P : MaximalSpectrum Γ(G.objects.left, ⊤),
      Module.finrank (Γ(G.objects.left, ⊤) ⧸ P.asIdeal)
        ((Γ(G.objects.left, ⊤) ⧸ P.asIdeal) ⊗[Γ(G.objects.left, ⊤)]
          Γ(G.arrows.left, ⊤)) = r := by
    by_cases hne : Nonempty (MaximalSpectrum Γ(G.objects.left, ⊤))
    · obtain ⟨P₀⟩ := hne
      refine ⟨G.source.left.finrank (G.objects.left.isoSpec.inv.base P₀.toPrimeSpectrum),
        fun P ↦ ?_⟩
      rw [finrank_quotient_tensor_eq_rankAtStalk]
      show G.source.left.appTop.hom.finrank P.toPrimeSpectrum = _
      refine (finrank_appTop G.source.left P.toPrimeSpectrum).trans ?_
      obtain ⟨a, ht, hs⟩ := (base_objectsToInvariantSpectrum_eq_iff G
        (G.objects.left.isoSpec.inv.base P.toPrimeSpectrum)
        (G.objects.left.isoSpec.inv.base P₀.toPrimeSpectrum)).mp
        (objectsToInvariantSpectrum_base_eq_of_maximal G P P₀)
      rw [← ht, ← hs]
      exact (source_finrank_eq G a).symm
    · exact ⟨0, fun P ↦ (hne ⟨P⟩).elim⟩
  let _ : Finite (MaximalSpectrum Γ(G.objects.left, ⊤)) := finite_maximalSpectrum_objectRing G
  let _ : Module.Free Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) :=
    Module.free_of_flat_of_finrank_eq Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) r hrank
  let _ : Algebra (invariantRing G) Γ(G.arrows.left, ⊤) := invariantRingAlgebraArrow G
  let _ : IsScalarTower (invariantRing G) Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hNset : ((LinearMap.range (targetAlgHom G).toLinearMap :
      Submodule (invariantRing G) Γ(G.arrows.left, ⊤)) : Set Γ(G.arrows.left, ⊤)) =
      Set.range (targetMap G) := by
    ext b
    show (∃ y, targetAlgHom G y = b) ↔ ∃ y, targetMap G y = b
    rfl
  obtain ⟨n, b, hb⟩ := contains_sBasis_of_generates (R := invariantRing G)
    (S := Γ(G.objects.left, ⊤)) (M := Γ(G.arrows.left, ⊤))
    (finite_maximalSpectrum_objectRing G)
    (map_maximalIdeal_le_jacobson _ (isIntegral_invariantRing G))
    (LinearMap.range (targetAlgHom G).toLinearMap)
    (by
      rw [GeneratesAsSModule, hNset]
      exact span_range_eq_top_of_lift_surjective (sourceAlgHom G) (targetAlgHom G)
        (tensorMap_surjective G))
  have hx (i : Fin n) : ∃ a, targetMap G a = b i := by
    rw [← hNset] at *
    exact hb i
  choose x hx using hx
  obtain ⟨bC, -⟩ := basis_over_invariantRing G x ⟨b, fun i ↦ (hx i).symm⟩
  obtain ⟨e, he⟩ := tensorProduct_equiv_arrowRing G x ⟨b, fun i ↦ (hx i).symm⟩
  exact ⟨n, bC, e, he⟩

/-- A finite basis of the object ring over the invariant ring makes the quotient map finite
locally free. -/
private alias isFiniteLocallyFree_objectsToInvariantSpectrum_of_basis :=
    AlgebraicGeometry.objectsToInvariantSpectrum_isFiniteLocallyFree_of_basis

/-- If the arrow ring is the tensor square of the object ring over the invariant ring, then the
arrow scheme is the kernel pair of the quotient map. -/
private theorem isPullback_objectsToInvariantSpectrum_of_tensorEquiv {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    (e : Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤) ≃+*
      Γ(G.arrows.left, ⊤))
    (he : ∀ a a', e (a ⊗ₜ[invariantRing G] a') = sourceMap G a * targetMap G a') :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) := by
  have hpush : IsPushout (CommRingCat.ofHom (Subring.subtype (invariantRing G)))
      (CommRingCat.ofHom (Subring.subtype (invariantRing G)))
      G.source.left.appTop G.target.left.appTop := by
    refine (CommRingCat.isPushout_tensorProduct (invariantRing G) Γ(G.objects.left, ⊤)
      Γ(G.objects.left, ⊤)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
      rfl rfl (CommRingCat.hom_ext ?_) (CommRingCat.hom_ext ?_)
    · ext a
      show e (a ⊗ₜ[invariantRing G] 1) = sourceMap G a
      rw [he, map_one, mul_one]
    · ext a
      show e (1 ⊗ₜ[invariantRing G] a) = targetMap G a
      rw [he, map_one, one_mul]
  refine IsPullback.flip ?_
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).of_iso' G.arrows.left.isoSpec
    G.objects.left.isoSpec G.objects.left.isoSpec (Iso.refl _)
    (Scheme.isoSpec_hom_naturality G.source.left)
    (Scheme.isoSpec_hom_naturality G.target.left) ?_ ?_ <;>
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- Over a local invariant ring with infinite residue field, the quotient map of an
equivalence relation is finite locally free and the arrow scheme is its kernel pair. -/
@[sga "3 V 4.1" "special case"]
private theorem finiteLocallyFree_and_isPullback_of_local_invariants {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] [IsLocalRing (invariantRing G)]
    [Infinite (IsLocalRing.ResidueField (invariantRing G))] :
    IsFiniteLocallyFree (objectsToInvariantSpectrum G) ∧
      IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
        (objectsToInvariantSpectrum G) := by
  obtain ⟨n, b, e, he⟩ := exists_basis_tensorEquiv_of_local_invariants G
  exact ⟨isFiniteLocallyFree_objectsToInvariantSpectrum_of_basis G b,
    isPullback_objectsToInvariantSpectrum_of_tensorEquiv G e he⟩

/-! ### Descending to an arbitrary invariant ring -/

/-- Base changing an equivalence relation along an extension of the invariant ring gives an
equivalence relation. -/
private theorem baseChange_isEquivalenceRelation {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source] {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] (H : AffineInvariantBaseChange G C') :
    IsEquivalenceRelation H.groupoid.target H.groupoid.source := by
  have hm {T : Over (Spec (.of C'))} (f g : T ⟶ H.groupoid.arrows)
      (ht : f ≫ H.groupoid.target = g ≫ H.groupoid.target)
      (hs : f ≫ H.groupoid.source = g ≫ H.groupoid.source) : f = g := by
    refine Over.OverMorphism.ext (H.arrows_isPullback.hom_ext ?_ ((Over.w f).trans (Over.w g).symm))
    refine arrows_hom_ext G _ _ ?_ ?_
    · simpa only [Over.comp_left, Category.assoc, ← H.projection_target] using
        congrArg (fun k : T ⟶ H.groupoid.objects ↦ k.left ≫ H.objectsProjection) ht
    · simpa only [Over.comp_left, Category.assoc, ← H.projection_source] using
        congrArg (fun k : T ⟶ H.groupoid.objects ↦ k.left ≫ H.objectsProjection) hs
  exact ⟨⟨{
    right_cancellation := fun {_} f g ht hs ↦ hm f g ht hs
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

/-- The structure morphism of the object scheme of a base-changed groupoid factors through its
own invariant spectrum by the canonical map to the invariant functions. -/
private theorem objectsToInvariantSpectrum_comp_specMap_canonicalMap {S : Scheme.{u}}
    {G : GroupoidScheme S} {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (H : AffineInvariantBaseChange G C') :
    objectsToInvariantSpectrum H.groupoid ≫
        Spec.map (CommRingCat.ofHom H.canonicalMapToInvariantFunctions) =
      H.groupoid.objects.hom := by
  rw [objectsToInvariantSpectrum, Category.assoc, ← Spec.map_comp]
  show H.groupoid.objects.left.toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (.of C')).inv ≫ H.groupoid.objects.hom.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  simp

/-- Base changing an equivalence relation along a flat local extension of the invariant ring
with infinite residue field makes its structure morphism finite locally free and exhibits its
arrow scheme as the kernel pair. -/
private theorem baseChange_finiteLocallyFree_and_isPullback {S : Scheme.{u}}
    {G : GroupoidScheme S} [IsEquivalenceRelation G.target G.source] {C' : Type u}
    [CommRing C'] [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C']
    [IsLocalRing C'] [Infinite (IsLocalRing.ResidueField C')]
    (H : AffineInvariantBaseChange G C') :
    IsFiniteLocallyFree H.groupoid.objects.hom ∧
      IsPullback H.groupoid.target.left H.groupoid.source.left H.groupoid.objects.hom
        H.groupoid.objects.hom := by
  let _ : IsAffine H.groupoid.objects.left := IsAffine.of_isIso H.objectsIso.hom
  let _ : IsAffine H.groupoid.arrows.left := IsAffine.of_isIso H.arrowsIso.hom
  let _ : IsFiniteLocallyFree H.groupoid.source.left := H.source_isFiniteLocallyFree
  let _ : IsFiniteLocallyFree H.groupoid.target.left := H.target_isFiniteLocallyFree
  let _ : IsEquivalenceRelation H.groupoid.target H.groupoid.source :=
    baseChange_isEquivalenceRelation H
  let e := RingEquiv.ofBijective H.canonicalMapToInvariantFunctions
    (canonicalMapToInvariantFunctions_bijective_of_flat H)
  let _ : IsLocalRing (invariantRing H.groupoid) := e.isLocalRing
  let _ : IsLocalHom e.toRingHom := isLocalHom_toRingHom e
  let _ : Infinite (IsLocalRing.ResidueField (invariantRing H.groupoid)) :=
    Infinite.of_injective (IsLocalRing.ResidueField.map e.toRingHom) (RingHom.injective _)
  obtain ⟨hf, hp⟩ := finiteLocallyFree_and_isPullback_of_local_invariants H.groupoid
  let _ : IsIso (Spec.map (CommRingCat.ofHom H.canonicalMapToInvariantFunctions)) := by
    show IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  have hcomp := objectsToInvariantSpectrum_comp_specMap_canonicalMap H
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp hf
    refine (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr ?_
    rw [← hcomp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · refine hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map (CommRingCat.ofHom H.canonicalMapToInvariantFunctions))) (by simp)
      (by simp) ?_ ?_ <;> simpa using hcomp

/-- Base changing an equivalence relation along a flat local extension of the invariant ring
with infinite residue field makes the object ring flat over that extension. -/
private theorem baseChange_module_flat {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source] {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')] (H : AffineInvariantBaseChange G C') :
    Module.Flat C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤)) := by
  obtain ⟨hf, -⟩ := baseChange_finiteLocallyFree_and_isPullback H
  let _ : Flat H.groupoid.objects.hom := IsFiniteLocallyFree.flat _
  let _ : Flat (objectSchemeBaseChange G C').hom := by
    rw [show (objectSchemeBaseChange G C').hom =
      H.objectsIso.inv ≫ H.groupoid.objects.hom from by
        rw [← H.objectsIso_over, Iso.inv_hom_id_assoc]]
    infer_instance
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤))))) := by
    rw [show Spec.map (CommRingCat.ofHom
        (algebraMap C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤)))) =
      Spec.map (Algebra.TensorProduct.comm (invariantRing G) Γ(G.objects.left, ⊤)
        C').toRingEquiv.toCommRingCatIso.hom ≫ (objectSchemeBaseChange G C').hom from by
          dsimp only [objectSchemeBaseChange, Over.mk_hom]
          rw [← Spec.map_comp]
          congr 1]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)

/-- For an equivalence relation with affine object and arrow schemes and finite locally free
source and target, the object ring is flat over the invariant ring. -/
private theorem module_flat_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    Module.Flat (invariantRing G) Γ(G.objects.left, ⊤) := by
  rw [flat_iff_flat_localizedModule_atMaximal]
  intro p _
  obtain ⟨C', _, _, _, _, _, _⟩ :=
    exists_flat_localRing_infinite_residueField (Localization.AtPrime p)
  let _ : Algebra (invariantRing G) C' :=
    ((algebraMap (Localization.AtPrime p) C').comp
      (algebraMap (invariantRing G) (Localization.AtPrime p))).toAlgebra
  let _ : IsScalarTower (invariantRing G) (Localization.AtPrime p) C' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Module.Flat (invariantRing G) C' :=
    Module.Flat.trans (invariantRing G) (Localization.AtPrime p) C'
  let _ : Module.FaithfullyFlat (Localization.AtPrime p) C' :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨H⟩ := exists_affineInvariantBaseChange G C'
  let _ : Module.Flat C' (C' ⊗[invariantRing G] Γ(G.objects.left, ⊤)) :=
    baseChange_module_flat H
  have hbc : Module.Flat C' (C' ⊗[Localization.AtPrime p]
      (Localization.AtPrime p ⊗[invariantRing G] Γ(G.objects.left, ⊤))) :=
    (Module.Flat.equiv_iff (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (invariantRing G) (Localization.AtPrime p) C' C' Γ(G.objects.left, ⊤))).mpr inferInstance
  exact (Module.Flat.equiv_iff
    (LocalizedModule.equivTensorProduct p.primeCompl Γ(G.objects.left, ⊤))).mpr
    ((Module.Flat.iff_flat_tensorProduct (Localization.AtPrime p) _ C').mp hbc)

/-! ### The arrow ring is the tensor square -/

/-- If the two scalar extensions of a pair of algebra maps form a cocartesian square, then the
scalar extension of the canonical map out of the tensor square is injective. -/
private theorem injective_map_lift_of_isPushout {C A B D : Type u} [CommRing C] [CommRing A]
    [CommRing B] [CommRing D] [Algebra C A] [Algebra C B] [Algebra C D] (f g : A →ₐ[C] B)
    (hp : IsPushout
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : D →ₐ[C] A ⊗[C] D).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : D →ₐ[C] A ⊗[C] D).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id C D)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map g (AlgHom.id C D)).toRingHom)) :
    Function.Injective (Algebra.TensorProduct.map
      (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _) (AlgHom.id C D)) := by
  have hw : CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : D →ₐ[C] A ⊗[C] D).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] A) (AlgHom.id C D)).toRingHom =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : D →ₐ[C] A ⊗[C] D).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : A →ₐ[C] A ⊗[C] A) (AlgHom.id C D)).toRingHom := by
    ext c
    simp
  refine Function.LeftInverse.injective (g := hp.desc _ _ hw) fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul d c =>
      induction d using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul a b =>
          have hab : Algebra.TensorProduct.map
              (Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _) (AlgHom.id C D)
              ((a ⊗ₜ[C] b) ⊗ₜ[C] c) =
              (Algebra.TensorProduct.map f (AlgHom.id C D)).toRingHom (a ⊗ₜ[C] c) *
                (Algebra.TensorProduct.map g (AlgHom.id C D)).toRingHom (b ⊗ₜ[C] 1) := by
            simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
            exact congrArg (fun z : B ↦ z ⊗ₜ[C] c)
              (Algebra.TensorProduct.lift_tmul f g (fun _ _ ↦ Commute.all _ _) a b)
          have hinl := congrArg (fun k : CommRingCat.of (A ⊗[C] D) ⟶
            CommRingCat.of ((A ⊗[C] A) ⊗[C] D) ↦ k.hom (a ⊗ₜ[C] c)) (hp.inl_desc _ _ hw)
          have hinr := congrArg (fun k : CommRingCat.of (A ⊗[C] D) ⟶
            CommRingCat.of ((A ⊗[C] A) ⊗[C] D) ↦ k.hom (b ⊗ₜ[C] 1)) (hp.inr_desc _ _ hw)
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
            CommRingCat.hom_ofHom] at hinl hinr
          rw [hab, map_mul, hinl, hinr]
          simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- After base change along a flat local extension with infinite residue field, the two scalar
extensions of the source and the target map form a cocartesian square. -/
private theorem isPushout_baseChange_sourceTarget {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source] {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')] (H : AffineInvariantBaseChange G C') :
    letI := invariantRingAlgebraArrow G
    IsPushout
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (sourceAlgHom G)
        (AlgHom.id (invariantRing G) C')).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (targetAlgHom G)
        (AlgHom.id (invariantRing G) C')).toRingHom) := by
  let _ := invariantRingAlgebraArrow G
  refine IsPullback.unop (IsPullback.of_map_of_faithful Scheme.Spec ?_)
  refine (baseChange_finiteLocallyFree_and_isPullback H).2.of_iso H.arrowsIso H.objectsIso
    H.objectsIso (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [H.target_eq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    congr 2
  · rw [H.source_eq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    congr 2
  · simpa [objectSchemeBaseChange] using H.objectsIso_over.symm
  · simpa [objectSchemeBaseChange] using H.objectsIso_over.symm

/-- After base change along a flat local extension with infinite residue field, the canonical
map from the tensor square of the object ring to the arrow ring stays injective. -/
private theorem baseChange_tensorMap_injective {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsEquivalenceRelation G.target G.source] {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')] (H : AffineInvariantBaseChange G C') :
    letI := invariantRingAlgebraArrow G
    Function.Injective (Algebra.TensorProduct.map
      (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G) fun _ _ ↦ Commute.all _ _)
      (AlgHom.id (invariantRing G) C')) := by
  let _ := invariantRingAlgebraArrow G
  exact injective_map_lift_of_isPushout (sourceAlgHom G) (targetAlgHom G)
    (isPushout_baseChange_sourceTarget H)

/-- If `1 ⊗ x` vanishes in `B ⊗[R] M`, then `1 ⊗ (1 ⊗ x)` vanishes in `B ⊗[A] (A ⊗[R] M)`. -/
private theorem one_tmul_one_tmul_eq_zero {R A B M : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M] (x : M) (h : (1 : B) ⊗ₜ[R] x = 0) :
    (1 : B) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] x) = 0 := by
  refine (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).injective ?_
  rwa [map_zero, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- An element of the tensor square of the object ring killed by the canonical map to the
arrow ring dies in every localization of the invariant ring at a maximal ideal. -/
private theorem one_tmul_eq_zero_of_lift_eq_zero {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source]
    (x : Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))
    (hx : letI := invariantRingAlgebraArrow G
      Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
        (fun _ _ ↦ Commute.all _ _) x = 0)
    (p : Ideal (invariantRing G)) [p.IsMaximal] :
    (1 : Localization.AtPrime p) ⊗ₜ[invariantRing G] x = 0 := by
  let _ := invariantRingAlgebraArrow G
  obtain ⟨C', _, _, _, _, _, _⟩ :=
    exists_flat_localRing_infinite_residueField (Localization.AtPrime p)
  let _ : Algebra (invariantRing G) C' :=
    ((algebraMap (Localization.AtPrime p) C').comp
      (algebraMap (invariantRing G) (Localization.AtPrime p))).toAlgebra
  let _ : IsScalarTower (invariantRing G) (Localization.AtPrime p) C' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Module.Flat (invariantRing G) C' :=
    Module.Flat.trans (invariantRing G) (Localization.AtPrime p) C'
  let _ : Module.FaithfullyFlat (Localization.AtPrime p) C' :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨H⟩ := exists_affineInvariantBaseChange G C'
  have hz : x ⊗ₜ[invariantRing G] (1 : C') = 0 := by
    refine baseChange_tensorMap_injective H ?_
    rw [map_zero]
    show Algebra.TensorProduct.map _ (AlgHom.id (invariantRing G) C')
      (x ⊗ₜ[invariantRing G] 1) = 0
    rw [Algebra.TensorProduct.map_tmul, hx, AlgHom.id_apply, TensorProduct.zero_tmul]
  have hz' : (1 : C') ⊗ₜ[invariantRing G] x = 0 := by
    simpa using congrArg (TensorProduct.comm (invariantRing G) _ C') hz
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff (Localization.AtPrime p)
    (Localization.AtPrime p ⊗[invariantRing G]
      (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))) _).mp
    (one_tmul_one_tmul_eq_zero x hz')

/-- For an equivalence relation with affine object and arrow schemes and finite locally free
source and target, the canonical map from the tensor square of the object ring to the arrow
ring is injective. -/
private theorem tensorMap_injective {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    letI := invariantRingAlgebraArrow G
    Function.Injective (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      fun _ _ ↦ Commute.all _ _) := by
  let _ := invariantRingAlgebraArrow G
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  exact Module.eq_zero_of_localization_maximal
    (fun p _ ↦ Localization.AtPrime p ⊗[invariantRing G]
      (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤)))
    (fun p _ ↦ TensorProduct.mk (invariantRing G) (Localization.AtPrime p) _ 1) x
    fun p hp ↦ one_tmul_eq_zero_of_lift_eq_zero G x hx p

/-! ### The quotient map is finite locally free and the relation is its kernel pair -/

/-- The arrow scheme of an equivalence relation is the kernel pair of the quotient map. -/
private theorem isPullback_kernelPair {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) := by
  let _ := invariantRingAlgebraArrow G
  refine isPullback_objectsToInvariantSpectrum_of_tensorEquiv G
    (RingEquiv.ofBijective (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      fun _ _ ↦ Commute.all _ _).toRingHom
      ⟨tensorMap_injective G, tensorMap_surjective G⟩) fun a b ↦ ?_
  exact Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _) a b

/-- The map of spectra induced by the inclusion of the invariant ring is flat. -/
private theorem flat_specMap_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    Flat (Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G)))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (module_flat_invariantRing G))

/-- The quotient map of an equivalence relation is flat. -/
private theorem flat_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    Flat (objectsToInvariantSpectrum G) := by
  have := flat_specMap_invariantRing G
  show Flat (G.objects.left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G))))
  infer_instance

/-- The quotient map of an equivalence relation is finite. -/
private theorem isFinite_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    IsFinite (objectsToInvariantSpectrum G) := by
  let _ : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
  let _ := invariantRingAlgebraArrow G
  let φ : (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤)) →ₐ[Γ(G.objects.left, ⊤)]
      Γ(G.arrows.left, ⊤) :=
    { toRingHom := (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
        fun _ _ ↦ Commute.all _ _).toRingHom
      commutes' := lift_tmul_one_eq_sourceMap G }
  let _ : IsFinite G.source.left := IsFiniteLocallyFree.isFinite _
  let _ : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := G.source.left.finite_appTop
  let _ : Module.Finite Γ(G.objects.left, ⊤)
      (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤)) :=
    Module.Finite.equiv (AlgEquiv.ofBijective φ
      ⟨tensorMap_injective G, tensorMap_surjective G⟩).symm.toLinearEquiv
  have := flat_specMap_invariantRing G
  let _ : Surjective (Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G)))) :=
    ⟨fun x ↦ by
      obtain ⟨y, hy⟩ := surjective_objectsToInvariantSpectrum G x
      exact ⟨G.objects.left.isoSpec.hom.base y, hy⟩⟩
  let _ : Module.FaithfullyFlat (invariantRing G) Γ(G.objects.left, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      ((flat_and_surjective_SpecMap_iff
        (CommRingCat.ofHom (Subring.subtype (invariantRing G)))).mp
        ⟨inferInstance, inferInstance⟩)
  let _ : Module.Finite (invariantRing G) Γ(G.objects.left, ⊤) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Γ(G.objects.left, ⊤)
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G)))) :=
    (IsFinite.SpecMap_iff _).mpr (show Module.Finite (invariantRing G) Γ(G.objects.left, ⊤) from
      inferInstance)
  show IsFinite (G.objects.left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G))))
  infer_instance

/-- The morphism from the object scheme to the spectrum of the invariant functions is finite
locally free. -/
@[stacks 03BM "finite locally free quotient map", sga "3 V 4.1" "affine case, (iv)"]
instance isFiniteLocallyFree_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    IsFiniteLocallyFree (objectsToInvariantSpectrum G) := by
  let _ : Flat (objectsToInvariantSpectrum G) := flat_objectsToInvariantSpectrum G
  let _ : IsFinite (objectsToInvariantSpectrum G) := isFinite_objectsToInvariantSpectrum G
  let _ : Surjective (objectsToInvariantSpectrum G) :=
    ⟨surjective_objectsToInvariantSpectrum G⟩
  let _ : LocallyOfFinitePresentation G.target.left :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      inferInstance |>.2.2
  refine (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨inferInstance, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyOfFinitePresentation) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_kernelPair G) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- The source and target maps exhibit the arrow scheme as the kernel pair of the morphism to
the spectrum of the invariant functions. -/
@[stacks 03BM "the relation is the kernel pair"]
theorem isPullback_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target.left G.source.left (objectsToInvariantSpectrum G)
      (objectsToInvariantSpectrum G) :=
  isPullback_kernelPair G

/-- The structure morphism of the object scheme descends along the morphism to the spectrum of
the invariant functions. -/
@[stacks 03BM "descent of the quotient over the base"]
def invariantSpectrumBaseMap {S : Scheme.{u}} (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    { f : Spec (.of (invariantRing G)) ⟶ S //
      objectsToInvariantSpectrum G ≫ f = G.objects.hom } := by
  obtain ⟨_, _, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (objectsToInvariantSpectrum G)).mp inferInstance
  let _ : Surjective (objectsToInvariantSpectrum G) :=
    (surjective_iff _).2 (surjective_objectsToInvariantSpectrum G)
  let _ : EffectiveEpi (objectsToInvariantSpectrum G) := inferInstance
  have hcompat : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ G.objects.left),
      g₁ ≫ objectsToInvariantSpectrum G = g₂ ≫ objectsToInvariantSpectrum G →
      g₁ ≫ G.objects.hom = g₂ ≫ G.objects.hom := by
    intro W g₁ g₂ hg
    calc
      g₁ ≫ G.objects.hom =
          ((isPullback_objectsToInvariantSpectrum G).lift g₁ g₂ hg ≫ G.target.left) ≫
            G.objects.hom := by
        rw [(isPullback_objectsToInvariantSpectrum G).lift_fst g₁ g₂ hg]
      _ = (isPullback_objectsToInvariantSpectrum G).lift g₁ g₂ hg ≫ G.arrows.hom := by
        rw [Category.assoc, ← G.target.w]
      _ = ((isPullback_objectsToInvariantSpectrum G).lift g₁ g₂ hg ≫ G.source.left) ≫
            G.objects.hom := by
        rw [Category.assoc, ← G.source.w]
      _ = g₂ ≫ G.objects.hom := by
        rw [(isPullback_objectsToInvariantSpectrum G).lift_snd g₁ g₂ hg]
  exact ⟨EffectiveEpi.desc _ G.objects.hom hcompat, EffectiveEpi.fac _ G.objects.hom hcompat⟩

/-- The spectrum of the invariant functions, as a scheme over the base. -/
def invariantSpectrumOver {S : Scheme.{u}} (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] : Over S :=
  Over.mk (invariantSpectrumBaseMap G).val

/-- The canonical projection from the object scheme to the invariant quotient over the base. -/
def toInvariantSpectrumOver {S : Scheme.{u}} (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    G.objects ⟶ invariantSpectrumOver G :=
  Over.homMk (objectsToInvariantSpectrum G) (invariantSpectrumBaseMap G).property

/-- The scheme underlying the invariant quotient over the base is the spectrum of the invariant
functions. -/
@[simp]
theorem invariantSpectrumOver_left {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    (invariantSpectrumOver G).left = Spec (.of (invariantRing G)) := rfl

/-- The morphism of schemes underlying the projection to the invariant quotient over the base
is the morphism to the spectrum of the invariant functions. -/
@[simp]
theorem toInvariantSpectrumOver_left {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    (toInvariantSpectrumOver G).left = objectsToInvariantSpectrum G := rfl

/-- Over the base scheme, the arrow scheme is the kernel pair of the projection to the
invariant quotient. -/
theorem isPullback_toInvariantSpectrumOver {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    IsPullback G.target G.source (toInvariantSpectrumOver G) (toInvariantSpectrumOver G) :=
  (isPullback_objectsToInvariantSpectrum G).of_map (Over.forget S) (Over.OverMorphism.ext
    (show G.target.left ≫ objectsToInvariantSpectrum G =
      G.source.left ≫ objectsToInvariantSpectrum G from
      (source_comp_objectsToInvariantSpectrum G).symm))

/-! ### Representation of the fppf quotient sheaf -/

/-- The projection to the invariant quotient coequalizes the target and the source of the
pre-relation attached to the groupoid. -/
theorem target_comp_toInvariantSpectrumOver {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source] :
    PreRelation.target (prod.lift G.target G.source) ≫ toInvariantSpectrumOver G =
      PreRelation.source (prod.lift G.target G.source) ≫ toInvariantSpectrumOver G := by
  apply Over.OverMorphism.ext
  simpa using (source_comp_objectsToInvariantSpectrum G).symm

/-- The spectrum of the invariant functions represents the fppf quotient sheaf of the
relation, and the representing isomorphism is compatible with the canonical projection from the
object scheme. -/
@[stacks 03BM "representation of the fppf quotient sheaf", sga "3 V 4.1" "affine case, (iv) fppf"]
theorem isIso_quotientSheafToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    ∃ hM : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
        (points (Over.post B.inclusion) (invariantSpectrumOver G)),
      IsIso (quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (prod.lift G.target G.source : PreRelation G.arrows G.objects)
        (toInvariantSpectrumOver G)
        (target_comp_toInvariantSpectrumOver G) hM) := by
  classical
  set j : PreRelation G.arrows G.objects := prod.lift G.target G.source with hj
  have hf : PreRelation.target j ≫ toInvariantSpectrumOver G =
      PreRelation.source j ≫ toInvariantSpectrumOver G :=
    target_comp_toInvariantSpectrumOver G
  refine ⟨isSheaf_points B S hS (invariantSpectrumOver G), ?_⟩
  let _ : IsFiniteLocallyFree (toInvariantSpectrumOver G).left :=
    isFiniteLocallyFree_objectsToInvariantSpectrum G
  obtain ⟨-, _, _⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (toInvariantSpectrumOver G).left).mp inferInstance
  let _ : Surjective (toInvariantSpectrumOver G).left :=
    (surjective_iff _).2 (surjective_objectsToInvariantSpectrum G)
  let k : G.arrows ⟶ pullback (toInvariantSpectrumOver G) (toInvariantSpectrumOver G) :=
    pullback.lift (PreRelation.target j) (PreRelation.source j) hf
  have hk : IsIso k := by
    have he : ((isPullback_toInvariantSpectrumOver G).isoIsPullback G.objects G.objects
        (IsPullback.of_hasPullback (toInvariantSpectrumOver G)
          (toInvariantSpectrumOver G))).hom = k := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        simp [hj, (isPullback_toInvariantSpectrumOver G).isoIsPullback_hom_fst G.objects
          G.objects (IsPullback.of_hasPullback _ _)]
      · rw [pullback.lift_snd]
        simp [hj, (isPullback_toInvariantSpectrumOver G).isoIsPullback_hom_snd G.objects
          G.objects (IsPullback.of_hasPullback _ _)]
    rw [← he]
    infer_instance
  let _ : IsIso k.left := by
    show IsIso ((Over.forget S).map k)
    infer_instance
  exact isIso_quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion) j
    (toInvariantSpectrumOver G) hf _
    (isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS
      (toInvariantSpectrumOver G))
    (isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS k)

end AlgebraicGeometry.GroupoidScheme

end

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Invariant.Profinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GroupActionsIntegral.Inertia
public import StacksFrontier.RingTheory.Etale.IntegralSplitting
public import StacksFrontier.RingTheory.Invariant.BaseChange
public import StacksFrontier.RingTheory.Invariant.Primes

/-!
# Inertia invariants are étale over the invariants

Let a finite group `G` act on a commutative ring `R` and let `q` be a prime of `R`. The inertia
subgroup `I` at `q` consists of the elements preserving `q` and acting as the identity modulo
`q`. The inclusion of the ring of invariants of `G` into the ring of invariants of `I` is étale
at the prime `R ^ I ∩ q`.

## Main results

* `MulSemiringAction.exists_etale_away_fixedPoints_inertia` (Stacks 0BST): the invariants of
  the inertia subgroup at `q` are étale over the invariants of `G` at the prime below `q`.

## Implementation notes

A ring map is étale at a prime of its target when it becomes étale after inverting a single
element outside that prime; this is the form the conclusion takes. The inertia subgroup is
Mathlib's `Ideal.inertia`, which asks that `g • x - x ∈ q` for every `x`; this also forces `g`
to preserve `q`, so it expresses both conditions in the displayed definition of `I`. The
algebra structure relating the two rings of invariants is induced by their inclusions into `R`.

The proof localizes on the invariants so that `R` splits as a product of rings each having a
single prime over `R ^ G ∩ q` with purely inseparable residue extension, after an étale base
change which changes neither the inertia subgroup nor the invariants. The product
decomposition is refined so that `G` permutes its factors, and then the invariants of `G` are
identified with the invariants of `I` on the factor containing `q`.

## References

* [Stacks Project, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST)
-/

@[expose] public section

namespace MulSemiringAction

open scoped Pointwise
open scoped TensorProduct

section

universe u

variable {G : Type*}

/-- Let `G` act on `S` permuting a finite family of complete orthogonal idempotents `e`
indexed by a `G`-set. An element fixed by the stabilizer of an index `j` agrees, after
multiplication by `e j`, with a `G`-invariant element of `S`. -/
private lemma exists_fixed_mul_idempotent_eq
    {S J : Type*} [CommRing S] [Group G] [MulSemiringAction G S]
    [Fintype J] [MulAction G J] (e : J → S)
    (he : CompleteOrthogonalIdempotents e)
    (heq : ∀ (g : G) (j : J), g • e j = e (g • j)) (j : J) (z : S)
    (hz : ∀ g : G, g • j = j → g • z = z) :
    ∃ t : S, (∀ g : G, g • t = t) ∧ t * e j = z * e j := by
  classical
  have hrep (g k : G) (h : g • j = k • j) :
      g • (z * e j) = k • (z * e j) := by
    have hkj : (k⁻¹ * g) • j = j := by
      rw [mul_smul, h]
      simp
    have hfix : (k⁻¹ * g) • (z * e j) = z * e j := by
      rw [smul_mul', hz _ hkj, heq, hkj]
    simpa only [smul_smul, mul_inv_cancel_left] using congrArg (k • ·) hfix
  let a (i : J) : S := if hi : ∃ g : G, g • j = i then
    hi.choose • (z * e j) else 0
  have ha (g : G) : a (g • j) = g • (z * e j) := by
    dsimp only [a]
    rw [dite_eq_left ⟨g, rfl⟩]
    exact hrep _ _ (Exists.choose_spec (show ∃ k : G, k • j = g • j from ⟨g, rfl⟩))
  have hequiv (g : G) (i : J) : g • a i = a (g • i) := by
    by_cases hi : ∃ k : G, k • j = i
    · obtain ⟨k, rfl⟩ := hi
      rw [← mul_smul g k j, ha, ha, mul_smul]
    · have hgi : ¬ ∃ k : G, k • j = g • i := by
        rintro ⟨k, hk⟩
        apply hi
        refine ⟨g⁻¹ * k, ?_⟩
        rw [mul_smul, hk, inv_smul_smul]
      simp [a, hi, hgi]
  refine ⟨∑ i, a i, ?_, ?_⟩
  · intro g
    show (MulSemiringAction.toRingHom G S g) (∑ i, a i) = _
    rw [map_sum]
    simp_rw [show ∀ i, (MulSemiringAction.toRingHom G S g) (a i) = a (g • i)
      from hequiv g]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  · rw [Finset.sum_mul, Finset.sum_eq_single j]
    · have haj : a j = z * e j := by simpa using ha (1 : G)
      rw [haj, mul_assoc, he.idem]
    · intro i _ hij
      by_cases hi : ∃ g : G, g • j = i
      · obtain ⟨g, rfl⟩ := hi
        rw [ha, smul_mul', heq, mul_assoc, he.ortho hij, mul_zero]
      · simp [a, hi]
    · simp

/-- Taking `K`-invariants commutes with a flat base change `A` of the invariant subring: a ring
map from `A ⊗[B] R ^ K` to `(A ⊗[B] R) ^ K` sending `a ⊗ r` to `a ⊗ r` is bijective. -/
@[sga "4 XVII 5.5.7.1" "special case"]
private lemma fixedPoints_tensorProduct_bijective
    {B R A K : Type*} [CommRing B] [CommRing R] [CommRing A]
    [Algebra B R] [Algebra B A] [Module.Flat B A]
    [Group K] [Finite K] [MulSemiringAction K R]
    [Algebra B (FixedPoints.subring R K)] [IsScalarTower B (FixedPoints.subring R K) R]
    [MulSemiringAction K (A ⊗[B] R)]
    (hbase : ∀ (g : K) (b : B), g • algebraMap B R b = algebraMap B R b)
    (hsmul : ∀ (g : K) (a : A) (r : R), g • (a ⊗ₜ[B] r) = a ⊗ₜ[B] (g • r))
    (φ : (A ⊗[B] FixedPoints.subring R K) →+* FixedPoints.subring (A ⊗[B] R) K)
    (hφ : ∀ a r, (φ (a ⊗ₜ[B] r) : A ⊗[B] R) = a ⊗ₜ[B] (r : R)) :
    Function.Bijective φ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let U := FixedPoints.subring R K
  let f : R →ₗ[B] K → R :=
    { toFun := fun r g => g • r
      map_add' := fun x y => by ext g; simp
      map_smul' := fun b r => by
        ext g
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, smul_mul', hbase] }
  let d : R →ₗ[B] K → R :=
    { toFun := fun r _ => r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let u : U ≃ₗ[B] LinearMap.eqLocus f d := LinearEquiv.ofBijective
    ({ toFun := fun r : U => (⟨r, funext r.property⟩ : LinearMap.eqLocus f d)
       map_add' := fun _ _ => rfl
       map_smul' := fun b r => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        show ((b • r : U) : R) = b • (r : R)
        simp only [Algebra.smul_def, Subring.coe_mul]
        have hc : ((algebraMap B U b : U) : R) = algebraMap B R b :=
          (IsScalarTower.algebraMap_apply B U R b).symm
        rw [hc] } : U →ₗ[B] LinearMap.eqLocus f d)
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z : LinearMap.eqLocus f d => (z : R)) h), fun r =>
      ⟨⟨r, fun g => congrFun r.property g⟩, rfl⟩⟩
  let E := u.lTensor A ≪≫ₗ
    (LinearMap.tensorEqLocusEquiv A A f d).restrictScalars B
  have hE (x : A ⊗[B] U) : (E x).val = (φ x).val := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simpa [E, u, LinearEquiv.ofBijective] using (hφ a r).symm
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  refine ⟨fun x y h => E.injective (Subtype.ext (by rw [hE, hE, h])), fun y => ?_⟩
  · have hy : y.val ∈ LinearMap.eqLocus
        (TensorProduct.AlgebraTensorModule.lTensor A A f)
        (TensorProduct.AlgebraTensorModule.lTensor A A d) := by
      rw [LinearMap.mem_eqLocus]
      apply (TensorProduct.piRight (R := B) (S := A) A (fun _ : K => R)).injective
      ext g
      have hf (x : A ⊗[B] R) :
          TensorProduct.piRight (R := B) (S := A) A (fun _ : K => R)
            (TensorProduct.AlgebraTensorModule.lTensor A A f x) g = g • x := by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a r => simpa [f] using (hsmul g a r).symm
        | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
      have hd (x : A ⊗[B] R) :
          TensorProduct.piRight (R := B) (S := A) A (fun _ : K => R)
            (TensorProduct.AlgebraTensorModule.lTensor A A d x) g = x := by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a r => simp [d]
        | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
      rw [hf, hd]
      exact y.property g
    obtain ⟨x, hx⟩ := E.surjective ⟨y, hy⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [← hE, hx]

/-- Two elements of `B` have the same image in the localization away from an idempotent `d` if
and only if they agree after multiplication by `d`. -/
private lemma localization_idempotent_eq_iff
    {B : Type*} [CommRing B] (d : B) (hd : IsIdempotentElem d) (x y : B) :
    algebraMap B (Localization.Away d) x = algebraMap B (Localization.Away d) y ↔
      d * x = d * y := by
  rw [IsLocalization.eq_iff_exists (Submonoid.powers d)]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    simpa only [← mul_assoc, ← pow_succ', hd.pow_succ_eq] using congrArg (d * ·) hn
  · exact fun h => ⟨⟨d, Submonoid.mem_powers d⟩, h⟩

/-- Suppose `A → S` identifies `A` with the `G`-invariants of `S`, that `G` permutes a finite
family `e` of complete orthogonal idempotents of `S`, that `H` is the stabilizer of an index `j`,
and that the sum of `e` over the orbit of `j` comes from an idempotent of `A`. Then `A` is étale
over the localization of `S ^ H` away from `e j`. -/
private lemma etale_localization_fixedPoints_of_orthogonalIdempotents
    {A S J : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Group G] [MulSemiringAction G S] [Fintype J] [MulAction G J]
    (H : Subgroup G) [Algebra A (FixedPoints.subring S H)]
    [IsScalarTower A (FixedPoints.subring S H) S]
    (hbase : ∀ (g : G) (a : A), g • algebraMap A S a = algebraMap A S a)
    (hinj : Function.Injective (algebraMap A S))
    (hsurj : ∀ z : S, (∀ g : G, g • z = z) → ∃ a : A, algebraMap A S a = z)
    (e : J → S) (he : CompleteOrthogonalIdempotents e)
    (heq : ∀ (g : G) (j : J), g • e j = e (g • j))
    (j : J) (hstab : MulAction.stabilizer G j = H)
    (d : FixedPoints.subring S H) (hd : (d : S) = e j)
    (o : Finset J) (ho : ∀ i, i ∈ o ↔ ∃ g : G, g • j = i)
    (c : A) (hc : algebraMap A S c = ∑ i ∈ o, e i)
    (hcid : IsIdempotentElem c) :
    Algebra.Etale A (Localization.Away d) := by
  classical
  let B := FixedPoints.subring S H
  let T := Localization.Away d
  have hdid : IsIdempotentElem d := by
    apply Subtype.ext
    show (d : S) * (d : S) = (d : S)
    rw [hd]
    exact he.idem j
  have hcoe (a : A) : ((algebraMap A B a : B) : S) = algebraMap A S a :=
    (IsScalarTower.algebraMap_apply A B S a).symm
  have hmul : algebraMap A S c * e j = e j := by
    rw [hc, Finset.sum_mul, Finset.sum_eq_single j (fun i _ hij => he.ortho hij)
      (fun hj => (hj ((ho j).mpr ⟨1, one_smul _ _⟩)).elim)]
    exact he.idem j
  have hsur : Function.Surjective (algebraMap A T) := by
    intro x
    obtain ⟨z, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem d hdid x
    obtain ⟨t, ht, htz⟩ := exists_fixed_mul_idempotent_eq e he heq j (z : S)
      (fun g hg => z.property ⟨g, hstab ▸ hg⟩)
    obtain ⟨a, ha⟩ := hsurj t ht
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B T]
    apply (localization_idempotent_eq_iff d hdid _ _).mpr
    apply Subtype.ext
    simpa only [Subring.coe_mul, hd, hcoe, ha, mul_comm] using htz
  have heqmap (a b : A) : algebraMap A T a = algebraMap A T b ↔ c * a = c * b := by
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply A B T,
      localization_idempotent_eq_iff d hdid]
    constructor
    · intro hab
      have hsel : e j * algebraMap A S a = e j * algebraMap A S b := by
        simpa only [Subring.coe_mul, hd, hcoe] using congrArg Subtype.val hab
      apply hinj
      rw [map_mul, map_mul, hc, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨g, rfl⟩ := (ho i).mp hi
      simpa only [smul_mul', heq, hbase] using congrArg (g • ·) hsel
    · intro hab
      have h := congrArg (algebraMap A S) hab
      simp only [map_mul] at h
      have hh' : e j * algebraMap A S a = e j * algebraMap A S b := by
        simpa only [← mul_assoc, mul_comm (e j) (algebraMap A S c), hmul] using
          congrArg (e j * ·) h
      apply Subtype.ext
      simpa only [Subring.coe_mul, hd, hcoe] using hh'
  let : IsLocalization.Away c T := IsLocalization.away_of_isIdempotentElem_of_mul
    hcid heqmap hsur
  exact Algebra.Etale.of_isLocalizationAway c

open AlgebraicGeometry CategoryTheory in
/-- In a tower `A → B → T` with both `A → T` and `B → T` étale, the map `A → B` is étale at the
contraction to `B` of any prime of `T`. -/
private lemma exists_etale_localization_of_etale_tower
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
    [Algebra.Etale A T] [Algebra.Etale B T] (Q : Ideal T) [Q.IsPrime] :
    ∃ b : B, b ∉ Q.under B ∧ Algebra.Etale A (Localization.Away b) := by
  let f : Spec (.of T) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B T))
  let q : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Etale f := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hcomp : f ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A T)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A B T).symm
  have : Etale (f ≫ q) := by
    rw [hcomp]
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hopen : IsOpen (Set.range f) := by
    simpa using f.isOpenMap _ isOpen_univ
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show f ⟨Q, inferInstance⟩ ∈ Set.range f from ⟨_, rfl⟩) hopen
  let U : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen b
  have : Surjective (f ∣_ U) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hsub y.property
    have hxU : f x ∈ U := by
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxU⟩, Subtype.ext ((morphismRestrict_base_coe f U ⟨x, hxU⟩).trans hx)⟩
  have : Etale ((f ∣_ U) ≫ U.ι ≫ q) := by
    rw [morphismRestrict_ι_assoc]
    exact inferInstanceAs (Etale ((f ⁻¹ᵁ U).ι ≫ (f ≫ q)))
  have : Etale (U.ι ≫ q) :=
    Stacks.Etale.etale_of_comp_of_fppf (f ∣_ U) (U.ι ≫ q)
  have : Etale ((basicOpenIsoSpecAway (R := .of B) b).inv ≫ U.ι ≫ q) := inferInstance
  have heq : (basicOpenIsoSpecAway (R := .of B) b).inv ≫ U.ι ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) := by
    dsimp only [U]
    rw [← basicOpenIsoSpecAway_hom_SpecMap b, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp]
    congr 1
  refine ⟨b, hb, ?_⟩
  apply RingHom.etale_algebraMap.mp
  apply (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap A (Localization.Away b)))).mp
  rw [← heq]
  infer_instance

/-- The idempotent `∏_{g ∈ G} g • e (f g)` attached to a choice `f` of an index for every
translate of a finite family `e` of idempotents. -/
private noncomputable def inertiaRefinement
    {R : Type*} [CommRing R] [Group G] [Fintype G] [MulSemiringAction G R]
    {n : ℕ} (e : Fin n → R) (f : G → Fin n) : R :=
  by
    classical
    exact ∏ g : G, g • e (f g)

/-- The refinement of a complete orthogonal family of idempotents by choice functions is again
a complete orthogonal family. -/
private lemma inertiaRefinement_complete
    {R : Type*} [CommRing R] [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G R]
    {n : ℕ} (e : Fin n → R)
    (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (inertiaRefinement (G := G) e) := by
  classical
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro f f' hff'
    obtain ⟨g, hneq⟩ : ∃ g : G, f g ≠ f' g := by
      by_contra h
      push Not at h
      exact hff' (funext h)
    show (∏ g : G, g • e (f g)) * (∏ g : G, g • e (f' g)) = 0
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_zero (Finset.mem_univ g)
    rw [← smul_mul']
    simp [he.ortho hneq]
  · classical
    calc
      (∑ f : G → Fin n, inertiaRefinement (G := G) e f) =
          ∏ g : G, ∑ i : Fin n, g • e i := by
        simpa [inertiaRefinement] using
          (Finset.sum_prod_piFinset (s := Finset.univ)
            (g := fun (g : G) (i : Fin n) => g • e i))
      _ = 1 := by
        apply Finset.prod_eq_one
        intro g hg
        show ∑ i : Fin n, (MulSemiringAction.toRingHom G R g) (e i) = 1
        rw [← map_sum, he.complete, map_one]

/-- Translation of a choice function by a group element, `f ↦ fun g ↦ f (h⁻¹ * g)`. -/
private def inertiaRefinementIndexShift [Group G] {n : ℕ} (h : G) (f : G → Fin n) : G → Fin n :=
  fun g ↦ f (h⁻¹ * g)

/-- The action of `G` on choice functions by translation. -/
@[instance_reducible]
private def inertiaRefinementIndexMulAction [Group G] {n : ℕ} :
    MulAction G (G → Fin n) where
  smul := inertiaRefinementIndexShift
  one_smul f := by
    change inertiaRefinementIndexShift (1 : G) f = f
    funext g
    simp [inertiaRefinementIndexShift]
  mul_smul h₁ h₂ f := by
    change inertiaRefinementIndexShift (h₁ * h₂) f =
      inertiaRefinementIndexShift h₁ (inertiaRefinementIndexShift h₂ f)
    funext g
    simp [inertiaRefinementIndexShift, mul_assoc]

attribute [local instance] inertiaRefinementIndexMulAction

/-- The refined idempotents are equivariant: acting by `h` on `inertiaRefinement e f`
translates the choice function `f` by `h`. -/
private lemma inertiaRefinement_smul_indexShift
    {R : Type*} [CommRing R] [Group G] [Fintype G] [MulSemiringAction G R]
    {n : ℕ} (e : Fin n → R) (h : G) (f : G → Fin n) :
    h • inertiaRefinement (G := G) e f =
      inertiaRefinement (G := G) e (inertiaRefinementIndexShift h f) := by
  classical
  show (MulSemiringAction.toRingHom G R h) (∏ g : G, g • e (f g)) = _
  rw [map_prod]
  calc
    (∏ g : G, h • (g • e (f g))) = ∏ g : G, (h * g) • e (f g) := by
      congr 1
      funext g
      rw [mul_smul]
    _ = ∏ g : G, g • e (f (h⁻¹ * g)) := by
      apply Finset.prod_bij (fun g _ ↦ h * g)
      · intro g hg
        simp
      · intro g₁ hg₁ g₂ hg₂ heq
        exact mul_left_cancel heq
      · intro g hg
        exact ⟨h⁻¹ * g, Finset.mem_univ _, by simp⟩
      · intro g hg
        simp

/-- Exactly one member of a finite complete orthogonal family of idempotents avoids a given
prime ideal. -/
private lemma existsUnique_not_mem_of_completeOrthogonalIdempotents
    {R ι : Type*} [CommRing R] [Fintype ι] (e : ι → R)
    (he : CompleteOrthogonalIdempotents e) (q : Ideal R) [q.IsPrime] :
    ∃! i, e i ∉ q := by
  classical
  have hex : ∃ i, e i ∉ q := by
    by_contra h
    push Not at h
    have hsum : (∑ i : ι, e i) ∈ q := q.sum_mem fun i _ => h i
    exact q.one_notMem (by simpa [he.complete] using hsum)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  rcases Ideal.IsPrime.mem_or_mem_of_mul_eq_zero ‹q.IsPrime› (he.ortho (Ne.symm hne))
    with hmem | hmem
  · exact hi hmem
  · exact hj hmem

/-- An element of the inertia subgroup of a prime `q` fixes the unique choice function whose
refined idempotent avoids `q`. -/
private lemma inertia_fixes_selected_refinementIndex
    {R : Type*} [CommRing R] [Group G] [Fintype G]
    [MulSemiringAction G R] {n : ℕ} (e : Fin n → R)
    (he : CompleteOrthogonalIdempotents e) (q : Ideal R) [q.IsPrime]
    (h : G) (hh : h ∈ q.inertia G) (f : G → Fin n)
    (hf : inertiaRefinement (G := G) e f ∉ q) : h • f = f := by
  classical
  have h_not_mem : inertiaRefinement (G := G) e (h • f) ∉ q := by
    intro hmem
    have hsmul : h • inertiaRefinement (G := G) e f =
        inertiaRefinement (G := G) e (h • f) :=
      inertiaRefinement_smul_indexShift (G := G) e h f
    rw [← hsmul] at hmem
    have hdiff : h • inertiaRefinement (G := G) e f -
        inertiaRefinement (G := G) e f ∈ q := by
      change ∀ x, h • x - x ∈ q at hh
      exact hh _
    exact hf (by simpa [sub_sub_cancel] using q.sub_mem hmem hdiff)
  obtain ⟨f₀, hf₀, hunique⟩ :=
    existsUnique_not_mem_of_completeOrthogonalIdempotents
      (inertiaRefinement (G := G) e) (inertiaRefinement_complete e he) q
  exact (hunique (h • f) h_not_mem).trans (hunique f hf).symm

/-- Extending a prime `P` of `S` not containing `x` to the localization away from `x` gives a
prime whose contraction is `P`. -/
private lemma isPrime_and_under_map_localization_away
    {S : Type*} [CommRing S] (P : Ideal S) [P.IsPrime] (x : S) (hx : x ∉ P) :
    (P.map (algebraMap S (Localization.Away x))).IsPrime ∧
      (P.map (algebraMap S (Localization.Away x))).under S = P := by
  have hdisj : Disjoint (Submonoid.powers x : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ hm
    exact hx (Ideal.IsPrime.mem_of_pow_mem (I := P) inferInstance m hm)
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) P inferInstance hdisj,
    IsLocalization.under_map_of_isPrime_disjoint (M := Submonoid.powers x)
      (S := Localization.Away x) inferInstance hdisj⟩

/-- The ring of invariants of a group action is the ring of invariants of the action on the
ring. -/
private instance isInvariant_fixedPoints_subring {R G : Type*} [CommRing R] [Group G]
    [MulSemiringAction G R] : Algebra.IsInvariant (FixedPoints.subring R G) R G :=
  ⟨fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- For a finite group acting on a ring, only finitely many primes lie over a given prime of
the invariant subring. -/
private lemma finite_primes_over_fixedPoints
    {R : Type*} {G : Type*} [CommRing R] [Group G] [Finite G]
    [MulSemiringAction G R] (q : Ideal R) [q.IsPrime] :
    Set.Finite {r : Ideal R | r.IsPrime ∧
      r.LiesOver (q.under (FixedPoints.subring R G))} := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let RG := FixedPoints.subring R G
  let : Algebra.IsIntegral RG R := Algebra.IsInvariant.isIntegral RG R G
  apply (Set.finite_range fun g : G ↦ g • q).subset
  intro r hr
  obtain ⟨hrp, hrover⟩ := hr
  have hunder : q.under RG = r.under RG := hrover.over
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq RG R G q r hunder
  exact ⟨g, hg.symm⟩

/-- For a finite group acting on a ring, the maximal separable subextension of the residue
field extension at a prime over the invariant subring is finite. -/
private lemma finite_separable_residueExtension
    {R : Type*} {G : Type*} [CommRing R] [Group G] [Finite G]
    [MulSemiringAction G R] (q : Ideal R) [q.IsPrime] :
    let RG := FixedPoints.subring R G
    let p := q.under RG
    letI : q.LiesOver p := ⟨rfl⟩
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    letI : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
    letI : Algebra p.ResidueField q.ResidueField := inferInstance
    letI : Algebra p.ResidueField (separableClosure p.ResidueField q.ResidueField) := inferInstance
    letI : Module p.ResidueField
      (separableClosure p.ResidueField q.ResidueField) := Algebra.toModule
    Module.Finite p.ResidueField (separableClosure p.ResidueField q.ResidueField) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let RG := FixedPoints.subring R G
  let : Algebra.IsIntegral RG R := Algebra.IsInvariant.isIntegral RG R G
  let p := q.under RG
  let : p.IsPrime := Ideal.IsPrime.under RG q
  let : q.LiesOver p := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  let : Algebra p.ResidueField q.ResidueField := inferInstance
  let : Algebra RG q.ResidueField :=
    ((algebraMap R q.ResidueField).comp (algebraMap RG R)).toAlgebra
  let : IsScalarTower RG R q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic p.ResidueField q.ResidueField := inferInstance
  let : Algebra (RG ⧸ p) (R ⧸ q) := Ideal.Quotient.algebraOfLiesOver q p
  let : Algebra (RG ⧸ p) q.ResidueField :=
    ((algebraMap (R ⧸ q) q.ResidueField).comp
      (algebraMap (RG ⧸ p) (R ⧸ q))).toAlgebra
  let : IsScalarTower (RG ⧸ p) (R ⧸ q) q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (RG ⧸ p) p.ResidueField := inferInstance
  let : IsScalarTower RG (RG ⧸ p) p.ResidueField := inferInstance
  let : IsScalarTower RG p.ResidueField q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    show algebraMap RG q.ResidueField x =
      Ideal.ResidueField.map p q RG.subtype rfl (algebraMap RG p.ResidueField x)
    rw [IsScalarTower.algebraMap_apply RG R q.ResidueField x]
    exact (Ideal.ResidueField.map_algebraMap p q RG.subtype rfl x).symm
  let : IsScalarTower (RG ⧸ p) p.ResidueField q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show algebraMap (R ⧸ q) q.ResidueField
      (algebraMap (RG ⧸ p) (R ⧸ q) (Ideal.Quotient.mk p x)) =
      algebraMap p.ResidueField q.ResidueField
        (algebraMap (RG ⧸ p) p.ResidueField (Ideal.Quotient.mk p x))
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.algebraMap_quotient_residueField_mk,
      Ideal.algebraMap_quotient_residueField_mk]
    calc
      algebraMap R q.ResidueField (algebraMap RG R x) = algebraMap RG q.ResidueField x :=
        (IsScalarTower.algebraMap_apply RG R q.ResidueField x).symm
      _ = algebraMap p.ResidueField q.ResidueField (algebraMap RG p.ResidueField x) :=
        IsScalarTower.algebraMap_apply RG p.ResidueField q.ResidueField x
  let : IsScalarTower p.ResidueField p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Normal p.ResidueField q.ResidueField :=
    Ideal.IsFractionRing.normal G p q p.ResidueField q.ResidueField
  let : Finite Gal(q.ResidueField/p.ResidueField) := by
    apply Finite.of_surjective (IsFractionRing.stabilizerHom G p q p.ResidueField q.ResidueField)
    exact IsFractionRing.stabilizerHom_surjective G p q p.ResidueField q.ResidueField
  let : Finite (q.ResidueField →ₐ[p.ResidueField] AlgebraicClosure q.ResidueField) :=
    Finite.of_equiv (Gal(q.ResidueField/p.ResidueField))
      (Normal.algHomEquivAut p.ResidueField (AlgebraicClosure q.ResidueField) q.ResidueField).symm
  let : Algebra p.ResidueField (separableClosure p.ResidueField q.ResidueField) := inferInstance
  let : Module p.ResidueField (separableClosure p.ResidueField q.ResidueField) :=
    Algebra.toModule
  have hpos : 0 < Field.finSepDegree p.ResidueField q.ResidueField := by
    rw [Field.finSepDegree_eq_of_isAlgClosed p.ResidueField q.ResidueField
      (AlgebraicClosure q.ResidueField)]
    exact Nat.card_pos
  have hrank : Module.rank p.ResidueField
      (separableClosure p.ResidueField q.ResidueField) < Cardinal.aleph0 := by
    by_contra h
    have hzero : Cardinal.toNat (Module.rank p.ResidueField
      (separableClosure p.ResidueField q.ResidueField)) = 0 :=
      Cardinal.toNat_apply_of_aleph0_le (not_lt.mp h)
    have hsep : Field.finSepDegree p.ResidueField q.ResidueField = 0 := by
      rw [Field.finSepDegree_eq, Field.sepDegree, hzero]
    omega
  let : Module.Free p.ResidueField (separableClosure p.ResidueField q.ResidueField) :=
    Module.Free.of_divisionRing p.ResidueField _
  exact (Module.rank_lt_aleph0_iff
    (R := p.ResidueField) (M := separableClosure p.ResidueField q.ResidueField)).mp hrank

/-- The same finiteness statement, for an arbitrary prime of the invariant subring equal to
the contraction of the given prime. -/
private lemma finite_separable_residueExtension_of_eq
    {R : Type*} {G : Type*} [CommRing R] [Group G] [Finite G]
    [MulSemiringAction G R] (q : Ideal R) [q.IsPrime]
    (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
    (hp : p = q.under (FixedPoints.subring R G)) :
    letI : q.LiesOver p := Ideal.LiesOver.mk hp
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    letI : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
    letI : Algebra p.ResidueField q.ResidueField := inferInstance
    Module.Finite p.ResidueField
      (separableClosure p.ResidueField q.ResidueField) := by
  cases hp
  simpa using finite_separable_residueExtension (G := G) q

end

variable {R G : Type*} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

/-- For a finite group acting on a ring, the inclusion of the invariant ring into the ring of
invariants of the inertia subgroup at a prime `q` is étale at the prime below `q`. -/
@[stacks 0BST]
public theorem exists_etale_away_fixedPoints_inertia (q : Ideal R) [q.IsPrime] :
    let I := q.inertia G
    let RG := FixedPoints.subring R G
    let RI := FixedPoints.subring R I
    letI : Algebra RG RI := (Subring.inclusion (by
      intro x hx g
      exact hx g)).toAlgebra
    ∃ g : RI, g ∉ q.comap RI.subtype ∧ Algebra.Etale RG (Localization.Away g) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let RG := FixedPoints.subring R G
  let : Algebra.IsIntegral RG R := Algebra.IsInvariant.isIntegral RG R G
  have hfinite : Set.Finite {r : Ideal R | r.IsPrime ∧ r.LiesOver (q.under RG)} :=
    finite_primes_over_fixedPoints (G := G) q
  have hseparable : ∀ (q' : Ideal R) (hq' : q'.IsPrime)
      (hqover : q'.LiesOver (q.under RG)),
      let := hq'
      let := hqover
      let := Localization.AtPrime.algebraOfLiesOver (q.under RG) q'
      Module.Finite (q.under RG).ResidueField
        (separableClosure (q.under RG).ResidueField q'.ResidueField) := by
    intro q' hq' hqover
    let : q'.IsPrime := hq'
    let : (q.under RG).IsPrime := Ideal.IsPrime.under RG q
    exact finite_separable_residueExtension_of_eq (G := G) q' (q.under RG) hqover.over
  obtain ⟨R', hR'Comm, hR'Algebra, hR'Etale, p', hp'Prime, hp'LiesOver, n, e, he, r,
      hrPrime, hrLiesOver, hFactorsIntegral, hUniquePrime, hPure⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable
      (q.under RG) hfinite hseparable
  let : CommRing R' := hR'Comm
  let : Algebra RG R' := hR'Algebra
  let : Algebra.Etale RG R' := hR'Etale
  let S := R' ⊗[RG] R
  let : MulAction G (G → Fin n) := inertiaRefinementIndexMulAction
  let : MulSemiringAction G S := MulSemiringAction.baseChangeMulSemiringAction
  let e' : (G → Fin n) → S := fun f => inertiaRefinement (G := G) e f
  have he' : CompleteOrthogonalIdempotents e' :=
    inertiaRefinement_complete (G := G) e he
  let : Algebra R' S := Algebra.TensorProduct.leftAlgebra
  let : Algebra R S := Algebra.TensorProduct.rightAlgebra
  have htmul (x : RG) :
      algebraMap RG R' x ⊗ₜ[RG] (1 : R) = (1 : R') ⊗ₜ[RG] algebraMap RG R x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (TensorProduct.tmul_smul (R := RG) x (1 : R') (1 : R)).symm
  let : IsScalarTower RG R S := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact htmul x)
  let : Algebra.IsIntegral R' S := inferInstance
  have hleft_injective : Function.Injective (algebraMap R' S) :=
    Algebra.TensorProduct.includeLeft_injective (R := RG) (A := R') (S := RG)
      Subtype.val_injective
  have hleft_ker : RingHom.ker (algebraMap R' S) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hleft_injective
  have hp'_prime : p'.IsPrime := hp'Prime
  obtain ⟨qS₀, hqS₀_bot, hqS₀_prime, hqS₀_under⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R') (S := S) p' ⊥ (by
      show Ideal.comap (algebraMap R' S) ⊥ ≤ p'
      rw [← RingHom.ker_eq_comap_bot, hleft_ker]
      exact bot_le)
  let r0 := qS₀.comap Algebra.TensorProduct.includeRight
  have hr_prime : r0.IsPrime := hqS₀_prime.comap _
  have hr_under : r0.under RG = q.under RG := by
    show Ideal.comap (algebraMap RG R) (Ideal.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[RG] S).toRingHom qS₀) = _
    rw [Ideal.comap_comap]
    have hcomp :
        (Algebra.TensorProduct.includeRight : R →ₐ[RG] S).toRingHom.comp
            (algebraMap RG R) =
          (algebraMap R' S).comp (algebraMap RG R') := by
      ext x
      exact (htmul x).symm
    rw [hcomp, ← Ideal.comap_comap,
      show Ideal.comap (algebraMap R' S) qS₀ = qS₀.under R' from rfl, hqS₀_under,
      hp'LiesOver.over]
  obtain ⟨g₀, hg₀⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq RG R G r0 q hr_under
  let qS := g₀ • qS₀
  have hqS_prime : qS.IsPrime := hqS₀_prime.smul g₀
  have hqS_under : qS.under R = q := by
    show (g₀ • qS₀).under R = q
    have hright_smul (g : G) (x : R) :
        g • (algebraMap R S x) = algebraMap R S (g • x) := by
      show g • ((1 : R') ⊗ₜ[RG] x) = (1 : R') ⊗ₜ[RG] (g • x)
      exact MulSemiringAction.baseChange_smul_tmul (A := R') g 1 x
    let : SMulDistribClass G R S := ⟨fun g x y => by
      show g • (algebraMap R S x * y) = algebraMap R S (g • x) * (g • y)
      rw [smul_mul', hright_smul]⟩
    rw [← Ideal.smul_under]
    show g₀ • r0 = q
    exact hg₀.symm
  let : MulSemiringAction G R' := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl
    smul_one := fun _ => rfl
    smul_mul := fun _ _ _ => rfl }
  have hleft_smul (g : G) (x : R') :
      g • (algebraMap R' S x) = algebraMap R' S x := by
    show MulSemiringAction.baseChangeAlgHom (G := G) (R := R) (A := R') g
      (x ⊗ₜ[RG] (1 : R)) = x ⊗ₜ[RG] (1 : R)
    rw [MulSemiringAction.baseChangeAlgHom, Algebra.TensorProduct.map_tmul]
    show x ⊗ₜ[RG] (g • (1 : R)) = x ⊗ₜ[RG] (1 : R)
    simp
  let : SMulCommClass G R' S := ⟨fun g x y => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hleft_smul]⟩
  have hqS_over : qS.LiesOver p' := by
    refine ⟨?_⟩
    show p' = (g₀ • qS₀).under R'
    rw [Ideal.under_smul]
    exact hqS₀_under.symm
  have hfqS_exists : ∃ f : G → Fin n, e' f ∉ qS := by
    exact (existsUnique_not_mem_of_completeOrthogonalIdempotents e' he' qS).exists
  obtain ⟨f, hf⟩ := hfqS_exists
  have hqS_inertia : q.inertia G = qS.inertia G := by
    apply MulSemiringAction.inertia_eq_inertia_baseChange (G := G) (R := R) (A := R') q qS
    show q = qS.comap Algebra.TensorProduct.includeRight
    exact hqS_under.symm
  have hfixI : ∀ h ∈ q.inertia G, h • f = f := by
    intro h hh
    apply inertia_fixes_selected_refinementIndex (G := G) e he qS h _ f hf
    rw [← hqS_inertia]
    exact hh
  let orbit : Finset (G → Fin n) := Finset.univ.image fun h : G => h • f
  have hmem_orbit (f' : G → Fin n) : f' ∈ orbit ↔ ∃ h : G, h • f = f' := by
    simp [orbit]
  have horbit_smul (h : G) : orbit.image (fun f' => h • f') = orbit := by
    ext f'
    rw [Finset.mem_image, hmem_orbit]
    constructor
    · rintro ⟨f'', hf'', rfl⟩
      obtain ⟨g, rfl⟩ := hmem_orbit f'' |>.mp hf''
      exact ⟨h * g, by simp [mul_smul]⟩
    · rintro ⟨g, rfl⟩
      refine ⟨h⁻¹ • (g • f), ?_, ?_⟩
      · exact hmem_orbit _ |>.mpr ⟨h⁻¹ * g, by simp [mul_smul]⟩
      · simp
  let c : S := Finset.sum orbit e'
  have hc_fixed (h : G) : h • c = c := by
    show (MulSemiringAction.toRingHom G S h) (Finset.sum orbit e') = _
    rw [map_sum]
    apply Finset.sum_bij (fun f' _ => h • f')
    · intro f' hf'
      have : h • f' ∈ orbit.image (fun x => h • x) :=
        Finset.mem_image.mpr ⟨f', hf', rfl⟩
      simpa only [horbit_smul h] using this
    · intro f₁ hf₁ f₂ hf₂ hEq
      simpa using congrArg (fun x => h⁻¹ • x) hEq
    · intro f' hf'
      rcases hmem_orbit f' |>.mp hf' with ⟨g, rfl⟩
      exact ⟨h⁻¹ • (g • f), hmem_orbit _ |>.mpr ⟨h⁻¹ * g, by simp [mul_smul]⟩,
        by simp⟩
    · intro f' hf'
      show h • e' f' = e' (h • f')
      exact inertiaRefinement_smul_indexShift (G := G) e h f'
  have hc_mul (x : G → Fin n) (hx : x ∈ orbit) : c * e' x = e' x := by
    dsimp [c]
    rw [Finset.sum_mul]
    calc
      _ = e' x * e' x := Finset.sum_eq_single_of_mem x hx (by
        intro y hy hne
        exact he'.ortho hne)
      _ = e' x := he'.idem x
  have hc_mul_selected : c * e' f = e' f :=
    hc_mul f ((hmem_orbit f).mpr ⟨1, one_smul _ _⟩)
  have hc_not_mem : c ∉ qS := by
    intro hc
    have : e' f ∈ qS := by
      rw [← hc_mul_selected]
      simpa [mul_comm] using qS.mul_mem_left (e' f) hc
    exact hf this
  let ι : R' →+* FixedPoints.subring S G := RingHom.codRestrict
    (Algebra.TensorProduct.includeLeftRingHom (R := RG))
    (FixedPoints.subring S G) (fun a h => by
      show h • (a ⊗ₜ[RG] (1 : R)) = a ⊗ₜ[RG] (1 : R)
      exact hleft_smul h a)
  let : MulSemiringAction G (R' ⊗[(FixedPoints.subring R G)] R) :=
    MulSemiringAction.baseChangeMulSemiringAction
  obtain ⟨hbij, -, -, -⟩ :=
    @FixedPoints.canonicalMap_to_invariants_bijective_of_flat_and_isIntegral_isHomeomorph
    R _ G _ _ _ R' _ _ (MulSemiringAction.baseChangeMulSemiringAction (G := G) (R := R) (A := R') )
    (fun g a r => MulSemiringAction.baseChange_smul_tmul (G := G) (R := R) (A := R') g a r)
  have hsurj : Function.Surjective ι := (hbij inferInstance).2
  obtain ⟨c', hc'⟩ := hsurj ⟨c, hc_fixed⟩
  have hc'_map : algebraMap R' S c' = c := congrArg Subtype.val hc'
  have hc'_not_mem : c' ∉ p' := by
    intro hp
    have hmem : algebraMap R' S c' ∈ qS := by
      show c' ∈ qS.under R'
      rw [← hqS_over.over]
      exact hp
    exact hc_not_mem (hc'_map ▸ hmem)
  have hc_idem : c * c = c := by
    dsimp [c]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    have h := hc_mul x hx
    rw [mul_comm] at h
    exact h
  have hc'_idem : c' * c' = c' := by
    apply (hbij inferInstance).1
    show ι (c' * c') = ι c'
    rw [map_mul]
    apply Subtype.ext
    show algebraMap R' S c' * algebraMap R' S c' = algebraMap R' S c'
    rw [hc'_map, hc_idem]
  let i : Fin n := f 1
  have hrefine_mem (P : Ideal S) [P.IsPrime] (hi : e i ∈ P) : e' f ∈ P := by
    have hprod : (∏ g : G, g • e (f g)) ∈ P := by
      apply (Ideal.IsPrime.prod_mem_iff).2
      exact ⟨1, Finset.mem_univ _, by simpa using hi⟩
    simpa [e', inertiaRefinement] using hprod
  have hi_factor : e i ∉ qS := by
    exact fun hi => hf (hrefine_mem qS hi)
  let qi : Ideal (Localization.Away (e i)) :=
    qS.map (algebraMap S (Localization.Away (e i)))
  obtain ⟨hqi_prime, hqi_under⟩ : qi.IsPrime ∧ qi.under S = qS :=
    isPrime_and_under_map_localization_away qS (e i) hi_factor
  have hqiOver : qi.LiesOver p' := by
    let : qi.LiesOver qS := ⟨hqi_under.symm⟩
    exact Ideal.LiesOver.trans qi qS p'
  have hqi_eq : qi = r i := hUniquePrime i qi hqi_prime hqiOver
  let : p'.IsPrime := hp'_prime
  let : qi.IsPrime := hqi_prime
  let : qi.LiesOver p' := hqiOver
  let : Algebra (Localization.AtPrime p') (Localization.AtPrime qi) :=
    Localization.AtPrime.algebraOfLiesOver p' qi
  let : Localization.AtPrime.IsLiesOverAlgebra p' qi := inferInstance
  let : (r i).IsPrime := hrPrime i
  let : (r i).LiesOver p' := hrLiesOver i
  let : Algebra (Localization.AtPrime p') (Localization.AtPrime (r i)) :=
    Localization.AtPrime.algebraOfLiesOver p' (r i)
  let : Localization.AtPrime.IsLiesOverAlgebra p' (r i) := inferInstance
  have hpureQi : IsPurelyInseparable p'.ResidueField qi.ResidueField := by
    clear_value qi
    cases hqi_eq
    exact hPure i
  let ρ : S →+* Localization.Away (e i) := algebraMap S _
  have hqScomap : qS = qi.comap ρ := hqi_under.symm
  have hres_bij : Function.Bijective (Ideal.ResidueField.map qS qi ρ hqScomap) :=
    RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization
        (Submonoid.powers (e i)) (Localization.Away (e i)))
      qS qi hqScomap
  let eRes : qS.ResidueField ≃+* qi.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map qS qi ρ hqScomap) hres_bij
  let : qS.IsPrime := hqS_prime
  let : qS.LiesOver p' := hqS_over
  let : Algebra (Localization.AtPrime p') (Localization.AtPrime qS) :=
    Localization.AtPrime.algebraOfLiesOver p' qS
  let : Localization.AtPrime.IsLiesOverAlgebra p' qS := inferInstance
  let : Algebra p'.ResidueField qS.ResidueField := inferInstance
  have hqSover : p' = qS.comap (algebraMap R' S) := hqS_over.over
  have hqiover : p' = qi.comap (ρ.comp (algebraMap R' S)) := by
    show p' = qi.under R'
    exact hqiOver.over
  let βS : p'.ResidueField →+* qS.ResidueField :=
    Ideal.ResidueField.map p' qS (algebraMap R' S) hqSover
  let βi : p'.ResidueField →+* qi.ResidueField :=
    Ideal.ResidueField.map p' qi (ρ.comp (algebraMap R' S)) hqiover
  let : Algebra R' qS.ResidueField :=
    ((algebraMap p'.ResidueField qS.ResidueField).comp
      (algebraMap R' p'.ResidueField)).toAlgebra
  let : Algebra R' qi.ResidueField :=
    ((algebraMap p'.ResidueField qi.ResidueField).comp
      (algebraMap R' p'.ResidueField)).toAlgebra
  let : IsScalarTower R' p'.ResidueField qS.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R' p'.ResidueField qi.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hβ : (Ideal.ResidueField.map qS qi ρ hqScomap).comp βS = βi := by
    apply IsFractionRing.ringHom_ext (A := R' ⧸ p')
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [βS, βi, Ideal.ResidueField.map_algebraMap]
  have hβS_alg : βS = algebraMap p'.ResidueField qS.ResidueField := rfl
  have hβi_alg : βi = algebraMap p'.ResidueField qi.ResidueField := rfl
  let eResAlg : qS.ResidueField ≃ₐ[p'.ResidueField] qi.ResidueField :=
    { toRingEquiv := eRes
      commutes' := fun x => by
        rw [← hβS_alg, ← hβi_alg]
        have hx := congrArg (fun φ : p'.ResidueField →+* qi.ResidueField => φ x) hβ
        show Ideal.ResidueField.map qS qi ρ hqScomap (βS x) = βi x
        simpa only [RingHom.comp_apply] using hx }
  have hpureQS : IsPurelyInseparable p'.ResidueField qS.ResidueField :=
    eResAlg.symm.isPurelyInseparable
  have stabilizer_le_inertia : ∀ h : G, h • f = f → h ∈ qS.inertia G := by
    intro h hh x
    have he_fixed : h • e' f = e' f := by
      calc
        h • e' f = e' (h • f) := inertiaRefinement_smul_indexShift (G := G) e h f
        _ = e' f := congrArg e' hh
    have hpres : h • qS = qS := by
      have hselected_not : e' f ∉ h • qS := by
        intro he
        have hx : h⁻¹ • e' f ∈ qS :=
          Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp he
        apply hf
        have he_inv_fixed : h⁻¹ • e' f = e' f := by
          calc
            h⁻¹ • e' f = h⁻¹ • (h • e' f) := congrArg (fun z => h⁻¹ • z) he_fixed.symm
            _ = e' f := by simp
        simpa [he_inv_fixed] using hx
      have hi_not : e i ∉ h • qS := by
        intro hi
        exact hselected_not (hrefine_mem (h • qS) hi)
      let qh : Ideal (Localization.Away (e i)) :=
        (h • qS).map (algebraMap S (Localization.Away (e i)))
      obtain ⟨hqh_prime, hqh_under⟩ : qh.IsPrime ∧ qh.under S = h • qS :=
        isPrime_and_under_map_localization_away (h • qS) (e i) hi_not
      have hqhOver : qh.LiesOver p' := by
        have hunder : (h • qS).under R' = p' := by
          rw [Ideal.under_smul]
          exact hqS_over.over.symm
        let : qh.LiesOver (h • qS) := ⟨hqh_under.symm⟩
        have : qh.LiesOver ((h • qS).under R') := inferInstance
        simpa [hunder] using this
      have hqh_eq : qh = r i := hUniquePrime i qh hqh_prime hqhOver
      calc
        h • qS = qh.under S := hqh_under.symm
        _ = qi.under S := congrArg (Ideal.under S) (hqh_eq.trans hqi_eq.symm)
        _ = qS := hqi_under
    have hinvpres : h⁻¹ • qS = qS := inv_smul_eq_iff.mpr hpres.symm
    have hcomap : qS = qS.comap (MulSemiringAction.toRingHom G S h) := by
      ext y
      show y ∈ qS ↔ h • y ∈ qS
      constructor
      · intro hy
        have hy' : h • y ∈ h • qS := Ideal.smul_mem_pointwise_smul h y qS hy
        simpa [hpres] using hy'
      · intro hy
        have hy' : h⁻¹ • (h • y) ∈ h⁻¹ • qS :=
          Ideal.smul_mem_pointwise_smul h⁻¹ (h • y) qS hy
        simpa [hinvpres] using hy'
    let γ : qS.ResidueField →+* qS.ResidueField :=
      Ideal.ResidueField.map qS qS (MulSemiringAction.toRingHom G S h) hcomap
    have hγβ : γ.comp βS = βS := by
      apply IsFractionRing.ringHom_ext (A := R' ⧸ p')
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp [γ, βS, Ideal.ResidueField.map_algebraMap, hleft_smul]
    let γAlg : qS.ResidueField →ₐ[p'.ResidueField] qS.ResidueField :=
      { toRingHom := γ
        commutes' := by
          intro y
          rw [← hβS_alg]
          have hy := congrArg (fun φ : p'.ResidueField →+* qS.ResidueField => φ y) hγβ
          show γ (βS y) = βS y
          simpa only [RingHom.comp_apply] using hy }
    have hγid : γAlg = AlgHom.id _ _ := Subsingleton.elim _ _
    have hγfix (z : qS.ResidueField) : γ z = z := by
      have h := congrArg (fun φ : qS.ResidueField →ₐ[p'.ResidueField] qS.ResidueField => φ z)
        hγid
      simpa [γAlg] using h
    have hmap (y : S) :
        γ (algebraMap S qS.ResidueField y) = algebraMap S qS.ResidueField (h • y) := by
      simp [γ, Ideal.ResidueField.map_algebraMap]
    have hres : algebraMap S qS.ResidueField (h • x) =
        algebraMap S qS.ResidueField x := by
      simpa only [hmap] using hγfix (algebraMap S qS.ResidueField x)
    show h • x - x ∈ qS
    rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, hres]
    simp
  have hstabilizer : MulAction.stabilizer G f = q.inertia G := by
    ext h
    show h • f = f ↔ h ∈ q.inertia G
    constructor
    · intro hh
      rw [hqS_inertia]
      exact stabilizer_le_inertia h hh
    · exact hfixI h
  let I := q.inertia G
  let RI := FixedPoints.subring R I
  let SI := FixedPoints.subring S I
  let : Algebra RG RI := (Subring.inclusion (by
    intro x hx g
    exact hx g)).toAlgebra
  let : IsScalarTower RG RI R := IsScalarTower.of_algebraMap_eq' rfl
  let l : R' →+* SI := RingHom.codRestrict (algebraMap R' S) SI
    (fun a g => hleft_smul g a)
  let : Algebra R' SI := l.toAlgebra
  let : IsScalarTower R' SI S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra RG SI := (l.comp (algebraMap RG R')).toAlgebra
  let : IsScalarTower RG R' SI := IsScalarTower.of_algebraMap_eq' rfl
  let k : RI →+* SI := RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight : R →ₐ[RG] S).toRingHom.comp RI.subtype) SI
    (fun a g => by
      show g.val • ((1 : R') ⊗ₜ[RG] (a : R)) = (1 : R') ⊗ₜ[RG] (a : R)
      exact (MulSemiringAction.baseChange_smul_tmul
          (G := G) (R := R) (A := R') g.val 1 (a : R)).trans
        (congrArg (fun x : R => (1 : R') ⊗ₜ[RG] x) (a.property g)))
  let : Algebra RI SI := k.toAlgebra
  let : IsScalarTower RG RI SI := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    exact htmul a
  let α : RI →ₐ[RG] SI := IsScalarTower.toAlgHom RG RI SI
  let φ : R' ⊗[RG] RI →ₐ[R'] SI := AlgHom.liftEquiv RG R' RI SI α
  have hφ (a : R') (r : RI) : (φ (a ⊗ₜ[RG] r) : S) = a ⊗ₜ[RG] (r : R) := by
    show (a ⊗ₜ[RG] (1 : R)) * ((1 : R') ⊗ₜ[RG] (r : R)) = _
    simp
  have hφbij : Function.Bijective φ := fixedPoints_tensorProduct_bijective
    (K := I) (B := RG) (R := R) (A := R')
    (fun g a => a.property g)
    (fun g a r => MulSemiringAction.baseChange_smul_tmul (G := G) (A := R') g.val a r)
    φ.toRingHom hφ
  let : Algebra RI (R' ⊗[RG] RI) := Algebra.TensorProduct.rightAlgebra
  let eRI : (R' ⊗[RG] RI) ≃ₐ[RI] SI :=
    { toRingEquiv := (AlgEquiv.ofBijective φ hφbij).toRingEquiv
      commutes' := fun r => Subtype.ext (hφ 1 r) }
  have : Algebra.Etale RI (R' ⊗[RG] RI) := Algebra.Etale.of_equiv
    ({ toRingEquiv := (Algebra.TensorProduct.comm RG RI R').toRingEquiv
       commutes' := fun _ => rfl } : (RI ⊗[RG] R') ≃ₐ[RI] (R' ⊗[RG] RI))
  have : Algebra.Etale RI SI := Algebra.Etale.of_equiv eRI
  let d : SI := ⟨e' f, fun g => by
    show g.val • e' f = e' f
    rw [inertiaRefinement_smul_indexShift]
    exact congrArg e' (hfixI g g.property)⟩
  have : Algebra.Etale R' (Localization.Away d) :=
    etale_localization_fixedPoints_of_orthogonalIdempotents I hleft_smul hleft_injective
      (fun z hz => by
        obtain ⟨a, ha⟩ := hsurj ⟨z, hz⟩
        exact ⟨a, congrArg Subtype.val ha⟩)
      e' he' (fun g f => inertiaRefinement_smul_indexShift e g f)
      f hstabilizer d rfl orbit hmem_orbit c' hc'_map hc'_idem
  let T := Localization.Away d
  have : Algebra.Etale RG T := Algebra.Etale.comp RG R' T
  have : Algebra.Etale RI T := Algebra.Etale.comp RI SI T
  let Q := qS.comap SI.subtype
  have hQ : Q.IsPrime := Ideal.IsPrime.comap _
  have hdQ : d ∉ Q := hf
  let QT := Q.map (algebraMap SI T)
  obtain ⟨hQT, hQTunder⟩ : QT.IsPrime ∧ QT.under SI = Q :=
    isPrime_and_under_map_localization_away Q d hdQ
  have hunderRI : QT.under RI = q.comap RI.subtype := by
    rw [← Ideal.under_under (A := RI) (B := SI), hQTunder]
    show (qS.comap SI.subtype).comap k = _
    rw [Ideal.comap_comap]
    show qS.comap ((Algebra.TensorProduct.includeRight : R →ₐ[RG] S).toRingHom.comp
      RI.subtype) = _
    rw [← Ideal.comap_comap]
    exact congrArg (Ideal.comap RI.subtype) hqS_under
  obtain ⟨b, hb, het⟩ := exists_etale_localization_of_etale_tower
    (A := RG) (B := RI) QT
  exact ⟨b, by simpa only [hunderRI] using hb, het⟩

end MulSemiringAction

end

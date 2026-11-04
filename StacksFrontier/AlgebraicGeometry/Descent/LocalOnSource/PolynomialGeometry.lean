module

public import Mathlib.RingTheory.Nullstellensatz
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Criterion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.AffineSpaceOrbits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.JacobianCriterion

/-!
# Affine space, coordinate shears and the sub-power graph

The endomorphism of affine space with coordinates `xᵢ - xᵢ ^ p` is étale wherever the residue
field of the image point has characteristic dividing `p`, and over a field the only nonempty
open subset of affine `d`-space, `d ≥ 2`, invariant under it and under the elementary
coordinate shears is the whole space. This file collects that geometry of affine space, in the
form in which the locality criteria for properties of morphisms of schemes and of algebraic
spaces use it.

## Main definitions

* `AlgebraicGeometry.affineSpaceCoordinateShearIso`: the elementary transformation of affine
  space over a base replacing the `i`-th coordinate by `xᵢ + xⱼ ^ d`, as an automorphism.
* `AlgebraicGeometry.affineSpaceSubPow`: the endomorphism of affine space over a base with
  coordinates `xᵢ - xᵢ ^ p`.
* `AlgebraicGeometry.affineSpaceAddTwoIso`: affine `(d + 2)`-space over a base is affine
  `2`-space over affine `d`-space over that base.

## Main results

* `AlgebraicGeometry.affineSpace_subPow_etaleAt`: the endomorphism with coordinates
  `xᵢ - xᵢ ^ p` is étale at a point of affine space whose image has residue field of
  characteristic dividing `p`.
* `AlgebraicGeometry.affineOpen_eq_univ_of_shear_and_sub_pow_invariant_ulift`: a nonempty open
  subset of affine `d`-space over a field, `d ≥ 2`, invariant under the coordinate shears and,
  in positive characteristic, under `Xᵢ ↦ Xᵢ - Xᵢ ^ p`, is everything.
* `AlgebraicGeometry.affineSpace_smooth_over`: affine space on a finite index type is smooth
  over its base.
* `AlgebraicGeometry.etaleAt_iff_exists_open`: a morphism is étale at a point exactly when its
  restriction to some open neighbourhood of that point is étale.

## Implementation notes

Étaleness of the endomorphism with coordinates `xᵢ - xᵢ ^ p` is proved by presenting its graph
as the zero scheme of the system `subPowGraphSituation` and applying the Jacobian criterion;
`subPowGraphRingEquiv` identifies that zero scheme with affine space again. The index type of
affine space is `ULift (Fin d)` wherever the ambient schemes must lie in a single universe.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open MvPolynomial in
/-- Imposing the relations `qᵢ(y) = xᵢ` on the polynomial ring in a second family of
variables `y` over `MvPolynomial ι R` recovers the polynomial ring in the `y`. -/
noncomputable def polynomialGraphEquiv
    {R ι : Type*} [CommRing R] (q : ι → MvPolynomial ι R) :
    (MvPolynomial ι (MvPolynomial ι R) ⧸
      Ideal.span (Set.range fun i => MvPolynomial.map C (q i) - C (X i))) ≃+*
      MvPolynomial ι R := by
  let I := Ideal.span (Set.range fun i => MvPolynomial.map C (q i) - C (X i))
  let ev : MvPolynomial ι (MvPolynomial ι R) →+* MvPolynomial ι R :=
    eval₂Hom (aeval q).toRingHom X
  have hev (i : ι) : ev (MvPolynomial.map C (q i) - C (X i)) = 0 := by
    have hmap : ev.comp (MvPolynomial.map C) = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [ev]
      · intro j; simp [ev]
    rw [map_sub, ← RingHom.comp_apply, hmap]
    simp [ev]
  let F : (MvPolynomial ι (MvPolynomial ι R) ⧸ I) →+* MvPolynomial ι R :=
    Ideal.Quotient.lift I ev fun _ ha =>
      (Ideal.span_le (I := RingHom.ker ev)).2 (Set.range_subset_iff.2 hev) ha
  let G : MvPolynomial ι R →+* (MvPolynomial ι (MvPolynomial ι R) ⧸ I) :=
    eval₂Hom ((Ideal.Quotient.mk I).comp (C.comp C)) (fun i => Ideal.Quotient.mk I (X i))
  have hFG : F.comp G = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [F, G, ev]
  have hGC (r : R) : G (C r) = Ideal.Quotient.mk I (C (C r)) := by simp [G]
  have hGX (i : ι) : G (X i) = Ideal.Quotient.mk I (X i) := by simp [G]
  have hGmap (r : MvPolynomial ι R) :
      G r = Ideal.Quotient.mk I (MvPolynomial.map C r) := by
    have he : G = (Ideal.Quotient.mk I).comp (MvPolynomial.map C) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [hGC]
      · intro i; simp [hGX]
    exact DFunLike.congr_fun he r
  have hrel (i : ι) : G (q i) = Ideal.Quotient.mk I (C (X i)) := by
    rw [hGmap, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hGF : G.comp F = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · have hc : (G.comp ev).comp C = (Ideal.Quotient.mk I).comp C := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [ev, hGC]
        · intro i
          simpa [ev] using hrel i
      intro r
      exact DFunLike.congr_fun hc r
    · intro i
      simp [F, ev, hGX]
  exact { F with
    invFun := G
    left_inv := fun x => DFunLike.congr_fun hGF x
    right_inv := fun x => DFunLike.congr_fun hFG x }

/-- At a prime containing `p`, the Jacobian matrix of the equations
`yᵢ - yᵢ ^ p - aᵢ` is the identity, hence has rank `n`. -/
lemma sub_pow_jacobian_rank
    {R : Type*} [CommRing R] (n p : ℕ) (a : Fin n → R)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hp : (p : MvPolynomial (Fin n) R) ∈ Q) :
    (Matrix.of fun i j : Fin n =>
      algebraMap (MvPolynomial (Fin n) R) Q.ResidueField
        (MvPolynomial.pderiv j (MvPolynomial.X i - MvPolynomial.X i ^ p -
          MvPolynomial.C (a i)))).rank = n := by
  have hp' : (p : Q.ResidueField) = 0 := by
    rw [← map_natCast (algebraMap (MvPolynomial (Fin n) R) Q.ResidueField)]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have heq : (Matrix.of fun i j : Fin n =>
      algebraMap (MvPolynomial (Fin n) R) Q.ResidueField
        (MvPolynomial.pderiv j (MvPolynomial.X i - MvPolynomial.X i ^ p -
          MvPolynomial.C (a i)))) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hp', hij, Pi.single_apply, Matrix.one_apply]
  rw [heq, Matrix.rank_one]
  simp

/-- The graph of the endomorphism with coordinates `xᵢ - xᵢ ^ p`, presented by the
equations `yᵢ - yᵢ ^ p - xᵢ` at a prime containing `p`, with its full-rank Jacobian. -/
noncomputable def subPowGraphSituation
    (R : Type*) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    FullRankJacobianSystem (MvPolynomial (Fin n) R) n n := by
  let ev : MvPolynomial (Fin n) (MvPolynomial (Fin n) R) →+*
      MvPolynomial (Fin n) R := MvPolynomial.eval₂Hom
    (MvPolynomial.aeval (R := R) (fun i : Fin n =>
      MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom MvPolynomial.X
  let Q := x.asIdeal.comap ev
  let a : Fin n → MvPolynomial (Fin n) R := MvPolynomial.X
  refine {
    equations := fun i => MvPolynomial.X i - MvPolynomial.X i ^ p - MvPolynomial.C (a i)
    prime := Q
    prime_isPrime := inferInstance
    equations_mem_prime := ?_
    jacobian_rank := ?_ }
  · intro i
    change ev _ ∈ x.asIdeal
    simp [ev, a]
  · exact sub_pow_jacobian_rank n p a Q (by simpa [Q, Ideal.mem_comap] using hp)

/-- The zero scheme of the system `subPowGraphSituation` is again affine `n`-space:
the quotient by the equation ideal is the polynomial ring. -/
noncomputable def subPowGraphRingEquiv
    (R : Type*) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    (MvPolynomial (Fin n) (MvPolynomial (Fin n) R) ⧸
      (subPowGraphSituation R n p x hp).equationIdeal) ≃+* MvPolynomial (Fin n) R := by
  let q := fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R) -
    MvPolynomial.X i ^ p
  have hI : (subPowGraphSituation R n p x hp).equationIdeal =
      Ideal.span (Set.range fun i : Fin n => MvPolynomial.map MvPolynomial.C (q i) -
        MvPolynomial.C (MvPolynomial.X i)) := by
    simp only [q, map_sub, map_pow, MvPolynomial.map_X]
    rfl
  exact (Ideal.quotEquivOfEq hI).trans (polynomialGraphEquiv q)

/-- The system `subPowGraphSituation` is étale over its base at the chosen point. -/
lemma subPowGraph_etaleAt
    (R : Type*) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    EtaleAt (subPowGraphSituation R n p x hp).over
      (subPowGraphSituation R n p x hp).point :=
  AlgebraicGeometry.FullRankJacobianSystem.etaleAt_of_square_jacobian_rank _ rfl

/-- A finite set invariant under a surjective self-map none of whose fibres is a
singleton is empty. -/
lemma eq_empty_of_finite_preimage_eq
    {α : Type*} (F : α → α) (hF : Function.Surjective F)
    (hfiber : ∀ x, ∃ y, y ≠ x ∧ F y = F x)
    {s : Set α} (hs : s.Finite) (hstable : F ⁻¹' s = s) : s = ∅ := by
  have hm : Set.MapsTo F s s := fun x hx => (Set.ext_iff.mp hstable x).mpr hx
  have hsurj : Set.SurjOn F s s := by
    intro y hy
    obtain ⟨x, rfl⟩ := hF y
    exact ⟨x, (Set.ext_iff.mp hstable x).mp hy, rfl⟩
  have hinj : Set.InjOn F s := ((hs.surjOn_iff_bijOn_of_mapsTo hm).mp hsurj).injOn
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hne, heq⟩ := hfiber x
  have hy : y ∈ s := by
    rw [← hstable]
    show F y ∈ s
    rw [heq]
    exact hm hx
  exact hne (hinj hy hx heq)

/-- Over an algebraically closed field the map `x ↦ x - x ^ p` is surjective for `p > 1`. -/
lemma sub_pow_surjective
    {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ} (hp : 1 < p) :
    Function.Surjective (fun x : k => x - x ^ p) := by
  intro a
  let q : Polynomial k := Polynomial.X - Polynomial.X ^ p - Polynomial.C a
  have hdeg : q.natDegree = p := by
    dsimp [q]
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp
  have hdeg' : q.degree ≠ 0 := by
    intro h
    have : q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    omega
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root q hdeg'
  exact ⟨b, sub_eq_zero.mp (by simpa [Polynomial.IsRoot, q] using hb)⟩

/-- A finite set of tuples over an algebraically closed field of characteristic `p`,
invariant under the coordinatewise map `vᵢ ↦ vᵢ - vᵢ ^ p`, is empty. -/
lemma finite_eq_empty_of_sub_pow_preimage_eq
    {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {ι : Type*} [Nonempty ι] {s : Set (ι → k)} (hs : s.Finite)
    (hstable : (fun v : ι → k => fun i => v i - v i ^ p) ⁻¹' s = s) : s = ∅ := by
  classical
  apply eq_empty_of_finite_preimage_eq _ _ _ hs hstable
  · intro v
    choose w hw using fun i => sub_pow_surjective (k := k) (Fact.out : p.Prime).one_lt (v i)
    exact ⟨w, funext hw⟩
  · intro v
    let i : ι := Classical.choice ‹Nonempty ι›
    refine ⟨Function.update v i (v i + 1), ?_, ?_⟩
    · intro h
      simpa using congrFun h i
    · ext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
        rw [add_pow_char, one_pow]
        ring
      · simp [Function.update_of_ne hji]

/-- A maximal ideal of a polynomial ring in finitely many variables has a finite zero
locus in any field extension of the coefficients. -/
lemma finite_zeroLocus_of_isMaximal
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι k)) [I.IsMaximal] :
    (MvPolynomial.zeroLocus K I).Finite := by
  let : Field (MvPolynomial ι k ⧸ I) := Ideal.Quotient.field I
  let : Module.Finite k (MvPolynomial ι k ⧸ I) :=
    finite_of_algHom_finiteType_of_isJacobsonRing
      (AlgHom.id k (MvPolynomial ι k ⧸ I))
  let F : MvPolynomial.zeroLocus K I → ((MvPolynomial ι k ⧸ I) →ₐ[k] K) :=
    fun x => Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.val) x.property
  have hinj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    have hi := DFunLike.congr_fun h (Ideal.Quotient.mk I (MvPolynomial.X i))
    change MvPolynomial.aeval (R := k) x.val (MvPolynomial.X i) =
      MvPolynomial.aeval (R := k) y.val (MvPolynomial.X i) at hi
    simpa using hi
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)

/-- The point of the spectrum attached to the tuple `vᵢ - vᵢ ^ p` is the image of the
point attached to `v` under the map induced by `Xᵢ ↦ Xᵢ - Xᵢ ^ p`. -/
lemma pointToPoint_sub_pow
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} (p : ℕ) (v : ι → K) :
    MvPolynomial.pointToPoint (k := k) (fun i => v i - v i ^ p) =
      PrimeSpectrum.comap
        (MvPolynomial.aeval (R := k)
          (fun i : ι => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom
        (MvPolynomial.pointToPoint (k := k) v) := by
  have heq : MvPolynomial.aeval (R := k) (fun i => v i - v i ^ p) =
      (MvPolynomial.aeval v).comp
        (MvPolynomial.aeval (fun i : ι => MvPolynomial.X i - MvPolynomial.X i ^ p)) := by
    ext i
    simp
  apply PrimeSpectrum.ext
  ext q
  simp only [MvPolynomial.pointToPoint, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rw [heq]
  rfl

/-- The field-valued points lying over a finite set of maximal ideals form a finite set. -/
lemma finite_preimage_pointToPoint_of_isMaximal
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} [Finite ι] {Z : Set (PrimeSpectrum (MvPolynomial ι k))}
    (hZ : Z.Finite) (hmax : ∀ q ∈ Z, q.asIdeal.IsMaximal) :
    (MvPolynomial.pointToPoint (k := k) (K := K) ⁻¹' Z).Finite := by
  have hf : (⋃ q ∈ Z, MvPolynomial.zeroLocus K q.asIdeal).Finite :=
    hZ.biUnion fun q hq => by
      let : q.asIdeal.IsMaximal := hmax q hq
      exact finite_zeroLocus_of_isMaximal q.asIdeal
  apply hf.subset
  intro v hv
  refine Set.mem_iUnion.mpr ⟨MvPolynomial.pointToPoint v,
    Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
  intro q hq
  exact MvPolynomial.mem_vanishingIdeal_singleton_iff v q |>.mp hq

/-- In characteristic `p`, an open subset of the spectrum whose complement is a finite set
of maximal ideals and which is invariant under `Xᵢ ↦ Xᵢ - Xᵢ ^ p` is everything. -/
lemma eq_univ_of_finite_compl_sub_pow_invariant
    {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {ι : Type*} [Finite ι] [Nonempty ι]
    {W : Set (PrimeSpectrum (MvPolynomial ι k))}
    (hfinite : Wᶜ.Finite) (hmax : ∀ q ∈ Wᶜ, q.asIdeal.IsMaximal)
    (hstable : PrimeSpectrum.comap
      (MvPolynomial.aeval (R := k)
        (fun i : ι => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom ⁻¹' W = W) :
    W = Set.univ := by
  have hs : (MvPolynomial.pointToPoint (k := k) (K := K) ⁻¹' Wᶜ).Finite :=
    finite_preimage_pointToPoint_of_isMaximal hfinite hmax
  have hstable' : (fun v : ι → K => fun i => v i - v i ^ p) ⁻¹'
      (MvPolynomial.pointToPoint (k := k) ⁻¹' Wᶜ) =
      MvPolynomial.pointToPoint (k := k) ⁻¹' Wᶜ := by
    ext v
    show MvPolynomial.pointToPoint (fun i => v i - v i ^ p) ∉ W ↔
      MvPolynomial.pointToPoint v ∉ W
    rw [pointToPoint_sub_pow]
    exact not_congr (Set.ext_iff.mp hstable (MvPolynomial.pointToPoint v))
  have hempty := finite_eq_empty_of_sub_pow_preimage_eq hs hstable'
  apply Set.eq_univ_of_forall
  intro q
  by_contra hq
  obtain ⟨v, hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K (hmax q hq)
  have hpoint : MvPolynomial.pointToPoint (k := k) v = q :=
    PrimeSpectrum.ext hv.symm
  have hmem : v ∈ MvPolynomial.pointToPoint (k := k) ⁻¹' Wᶜ := by
    show MvPolynomial.pointToPoint v ∉ W
    rwa [hpoint]
  rw [hempty] at hmem
  exact hmem

/-- A nonempty open subset of affine `n`-space, `n ≥ 2`, invariant under every elementary
coordinate shear and, in positive characteristic, under `Xᵢ ↦ Xᵢ - Xᵢ ^ p`, is everything. -/
lemma affineOpen_eq_univ_of_shear_and_sub_pow_invariant
    {k : Type*} [Field k] {n : ℕ} (hn : 2 ≤ n)
    (W : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))
    (hopen : IsOpen W) (hne : W.Nonempty)
    (hshear : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ),
      PrimeSpectrum.comap
        (MvPolynomial.coordinateShear (R := k) i j hij d).toRingHom ⁻¹' W = W)
    (hfrob : 0 < ringChar k → PrimeSpectrum.comap
      (MvPolynomial.aeval (R := k) (fun i : Fin n =>
        MvPolynomial.X i - MvPolynomial.X i ^ ringChar k)).toRingHom ⁻¹' W = W) :
    W = Set.univ := by
  rcases MvPolynomial.eq_univ_or_finite_compl_of_invariant_coordinateShear
      hn W hopen hne hshear with hfull | ⟨hchar, hfinite, hmax⟩
  · exact hfull
  · have : NeZero (ringChar k) := ⟨Nat.ne_of_gt hchar⟩
    have : Fact (ringChar k).Prime := CharP.char_is_prime_of_pos k (ringChar k)
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact eq_univ_of_finite_compl_sub_pow_invariant (K := AlgebraicClosure k)
      hfinite (fun q hq => (hmax q hq).1) (hfrob hchar)

/-- If `j` is an open immersion and `j ≫ f` is étale at a point, then `f` is étale at the
image of that point. -/
lemma etaleAt_of_open_precomp {X' X Y : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (x' : X')
    (h : EtaleAt (j ≫ f) x') :
    EtaleAt f (j x') := by
  obtain ⟨A, hA, hx'A, V, hV, hAV, hEt⟩ := h
  let W : X.Opens := j ''ᵁ A
  have hW : IsAffineOpen W := j.isAffineOpen_iff_of_isOpenImmersion.mpr hA
  have hWV : W ≤ f ⁻¹ᵁ V := by rintro z ⟨a, ha, rfl⟩; exact hAV ha
  let e : A.toScheme ≅ W.toScheme := j.isoImage A
  let : IsAffine W.toScheme := hW
  let : IsAffine V.toScheme := hV
  have : Etale ((j ≫ f).resLE V A hAV) := etale_resLE_of_appLE_etale _ A hA V hV hAV hEt
  have heq : e.inv ≫ (j ≫ f).resLE V A hAV = f.resLE V W hWV := by
    apply (cancel_mono V.ι).1
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
      (Scheme.Hom.isoImage_inv_ι j A)
  have hresW : Etale (f.resLE V W hWV) := by rw [← heq]; infer_instance
  exact ⟨W, hW, ⟨x', hx'A, rfl⟩, V, hV, hWV,
    (RingHom.Etale.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V W hWV)).1
        ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hresW)⟩

/-- A morphism is étale at a point exactly when its restriction to some open neighbourhood
of the point is étale. -/
lemma etaleAt_iff_exists_open {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    EtaleAt f x ↔
      ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  constructor
  · intro h
    obtain ⟨U, -, hx, hU⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f x h
    exact ⟨U, hx, hU⟩
  · rintro ⟨U, hx, h⟩
    exact etaleAt_of_open_precomp U.ι f ⟨x, hx⟩
      ((etale_iff_forall_etaleAt _).mp h ⟨x, hx⟩)

/-- Postcomposing with an étale morphism preserves étaleness at a point. -/
lemma etaleAt_postcomp {X Y Z : Scheme.{u}} {f : X ⟶ Y}
    (g : Y ⟶ Z) [Etale g] (x : X)
    (h : EtaleAt f x) :
    EtaleAt (f ≫ g) x := by
  obtain ⟨U, hx, hU⟩ := (etaleAt_iff_exists_open f x).mp h
  have := hU
  exact (etaleAt_iff_exists_open _ x).mpr ⟨U, hx, by
    rw [← Category.assoc]; infer_instance⟩

/-- Under `subPowGraphRingEquiv` the structure map of the zero scheme becomes the
endomorphism `Xᵢ ↦ Xᵢ - Xᵢ ^ p` of the polynomial ring. -/
lemma subPowGraphRingEquiv_algebraMap
    (R : Type u) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    (subPowGraphRingEquiv R n p x hp).toRingHom.comp
        (algebraMap (MvPolynomial (Fin n) R)
          (MvPolynomial (Fin n) (MvPolynomial (Fin n) R) ⧸
            (subPowGraphSituation R n p x hp).equationIdeal)) =
      (MvPolynomial.aeval (R := R) (fun i : Fin n =>
        MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom := by
  show (subPowGraphRingEquiv R n p x hp).toRingHom.comp
      ((Ideal.Quotient.mk _).comp MvPolynomial.C) = _
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [subPowGraphRingEquiv, polynomialGraphEquiv, Ideal.quotEquivOfEq_mk]
  · intro i
    simp [subPowGraphRingEquiv, polynomialGraphEquiv, Ideal.quotEquivOfEq_mk]

/-- The isomorphism `subPowGraphRingEquiv` carries the chosen prime to the distinguished
point of the zero scheme. -/
lemma subPowGraphRingEquiv_point
    (R : Type u) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    (Spec.map (CommRingCat.ofHom (subPowGraphRingEquiv R n p x hp).toRingHom)) x =
      (subPowGraphSituation R n p x hp).point := by
  let S := subPowGraphSituation R n p x hp
  apply PrimeSpectrum.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk S.equationIdeal)
    Ideal.Quotient.mk_surjective
  show Ideal.comap (Ideal.Quotient.mk S.equationIdeal)
      (x.asIdeal.comap (subPowGraphRingEquiv R n p x hp).toRingHom) =
    Ideal.comap (Ideal.Quotient.mk S.equationIdeal)
      (S.prime.map (Ideal.Quotient.mk S.equationIdeal))
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  have hk : Ideal.comap (Ideal.Quotient.mk S.equationIdeal) ⊥ ≤ S.prime := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact Ideal.span_le.mpr (Set.range_subset_iff.mpr S.equations_mem_prime)
  rw [sup_of_le_left hk, Ideal.comap_comap]
  have hev : (subPowGraphRingEquiv R n p x hp).toRingHom.comp
      (Ideal.Quotient.mk S.equationIdeal) = MvPolynomial.eval₂Hom
        (MvPolynomial.aeval (R := R) (fun i : Fin n =>
          MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom MvPolynomial.X := by
    apply RingHom.ext
    intro q
    simp [S, subPowGraphRingEquiv, polynomialGraphEquiv, Ideal.quotEquivOfEq_mk]
  rw [hev]
  rfl

/-- The endomorphism of `Spec (MvPolynomial (Fin n) R)` with coordinates `Xᵢ - Xᵢ ^ p` is
étale at every point whose prime contains `p`. -/
lemma spec_sub_pow_etaleAt
    (R : Type u) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hp : (p : MvPolynomial (Fin n) R) ∈ x.asIdeal) :
    EtaleAt
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
        (fun i : Fin n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)) x := by
  let S := subPowGraphSituation R n p x hp
  let e := Scheme.Spec.mapIso (subPowGraphRingEquiv R n p x hp).toCommRingCatIso.op
  let t : Spec (.of (MvPolynomial (Fin n) R)) ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
      (fun i : Fin n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)
  have he : e.hom ≫ S.over = t := by
    show Spec.map (CommRingCat.ofHom (subPowGraphRingEquiv R n p x hp).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) R) _)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
      (subPowGraphRingEquiv_algebraMap R n p x hp)
  have he' : e.inv ≫ t = S.over := by rw [← he]; simp
  have h := etaleAt_of_open_precomp e.inv t S.point (by
    rw [he']; exact subPowGraph_etaleAt R n p x hp)
  have hx : e.inv S.point = x := by
    rw [← subPowGraphRingEquiv_point R n p x hp]
    exact congrArg (fun f => f x) e.hom_inv_id
  rwa [hx] at h

/-- The base change of a morphism étale at the image of a point is étale at that point. -/
lemma etaleAt_of_isPullback
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback a b f g) (z : X')
    (hz : EtaleAt f (a z)) :
    EtaleAt b z := by
  obtain ⟨U, hzU, hU⟩ := (etaleAt_iff_exists_open f (a z)).mp hz
  have := hU
  have hp := (isPullback_morphismRestrict a U).paste_vert h
  apply (etaleAt_iff_exists_open b z).mpr
  refine ⟨a ⁻¹ᵁ U, hzU, ?_⟩
  rw [← hp.isoPullback_hom_snd]
  infer_instance

/-- The endomorphism of `Spec (MvPolynomial (ULift (Fin n)) R)` with coordinates
`Xᵢ - Xᵢ ^ p` is étale at every point whose prime contains `p`. -/
lemma spec_sub_pow_etaleAt_ulift
    (R : Type u) [CommRing R] (n p : ℕ)
    (x : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin n)) R))
    (hp : (p : MvPolynomial (ULift.{u} (Fin n)) R) ∈ x.asIdeal) :
    EtaleAt
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
        (fun i : ULift.{u} (Fin n) => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)) x := by
  let e := MvPolynomial.renameEquiv R (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
  let E := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let t : Spec (.of (MvPolynomial (ULift.{u} (Fin n)) R)) ⟶
      Spec (.of (MvPolynomial (ULift.{u} (Fin n)) R)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
      (fun i : ULift.{u} (Fin n) => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)
  let t₀ : Spec (.of (MvPolynomial (Fin n) R)) ⟶
      Spec (.of (MvPolynomial (Fin n) R)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
      (fun i : Fin n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)
  have hc : E.inv ≫ t = t₀ ≫ E.inv := by
    dsimp [E, t, t₀]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e]
    · intro i; simp [e, MvPolynomial.renameEquiv_apply]
  have h₀ := spec_sub_pow_etaleAt R n p (E.hom x) (by
    show e (p : MvPolynomial (Fin n) R) ∈ x.asIdeal
    simpa using hp)
  have h := etaleAt_of_open_precomp E.inv t (E.hom x) (by
    rw [hc]; exact etaleAt_postcomp E.inv _ h₀)
  have he : E.inv (E.hom x) = x := congrArg (fun f => f x) E.hom_inv_id
  rwa [he] at h

/-- The elementary transformation of affine space over `S` replacing the `i`-th coordinate
by `xᵢ + xⱼ ^ d` and fixing the others. -/
noncomputable def affineSpaceCoordinateShear
    {S : Scheme.{u}} {n : Type u} [DecidableEq n]
    (i j : n) (_hij : i ≠ j) (d : ℕ) :
    AffineSpace n S ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (AffineSpace n S ↘ S) fun l =>
    if l = i then AffineSpace.coord S i + AffineSpace.coord S j ^ d
    else AffineSpace.coord S l

/-- The elementary transformation of affine space over `S` replacing the `i`-th coordinate
by `xᵢ - xⱼ ^ d`, inverse to `affineSpaceCoordinateShear`. -/
noncomputable def affineSpaceCoordinateShearInv
    {S : Scheme.{u}} {n : Type u} [DecidableEq n]
    (i j : n) (_hij : i ≠ j) (d : ℕ) :
    AffineSpace n S ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (AffineSpace n S ↘ S) fun l =>
    if l = i then AffineSpace.coord S i - AffineSpace.coord S j ^ d
    else AffineSpace.coord S l

/-- The elementary coordinate shear as an automorphism of affine space over `S`. -/
noncomputable def affineSpaceCoordinateShearIso
    {S : Scheme.{u}} {n : Type u} [DecidableEq n]
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    AffineSpace n S ≅ AffineSpace n S where
  hom := affineSpaceCoordinateShear i j hij d
  inv := affineSpaceCoordinateShearInv i j hij d
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp [affineSpaceCoordinateShear, affineSpaceCoordinateShearInv]
    · intro l
      simp only [affineSpaceCoordinateShear, affineSpaceCoordinateShearInv,
        AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord]
      by_cases hl : l = i
      · subst l
        simp [Ne.symm hij]
      · simp [hl]
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp [affineSpaceCoordinateShear, affineSpaceCoordinateShearInv]
    · intro l
      simp only [affineSpaceCoordinateShear, affineSpaceCoordinateShearInv,
        AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord]
      by_cases hl : l = i
      · subst l
        simp [Ne.symm hij]
      · simp [hl]

/-- Coordinate shears commute with the morphism of affine spaces induced by a morphism of
base schemes. -/
lemma affineSpace_map_comm_coordinateShear
    {S T : Scheme.{u}} {n : Type u} [DecidableEq n]
    (f : S ⟶ T) (i j : n) (hij : i ≠ j) (d : ℕ) :
    AffineSpace.map n f ≫ affineSpaceCoordinateShear i j hij d =
      affineSpaceCoordinateShear i j hij d ≫ AffineSpace.map n f := by
  apply AffineSpace.hom_ext
  · simp [affineSpaceCoordinateShear, AffineSpace.map_over, Category.assoc]
  · intro l
    by_cases hl : l = i
    · subst l
      show (AffineSpace.map n f).appTop
          ((affineSpaceCoordinateShear i j hij d).appTop (AffineSpace.coord T i)) =
        (affineSpaceCoordinateShear i j hij d).appTop
          ((AffineSpace.map n f).appTop (AffineSpace.coord T i))
      simp [affineSpaceCoordinateShear, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.map_appTop_coord]
    · show (AffineSpace.map n f).appTop
          ((affineSpaceCoordinateShear i j hij d).appTop (AffineSpace.coord T l)) =
        (affineSpaceCoordinateShear i j hij d).appTop
          ((AffineSpace.map n f).appTop (AffineSpace.coord T l))
      simp [affineSpaceCoordinateShear, hl, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.map_appTop_coord]

/-- The endomorphism of affine space over `S` with coordinates `xᵢ - xᵢ ^ p`. -/
noncomputable def affineSpaceSubPow
    {S : Scheme.{u}} {n : Type u} (p : ℕ) :
    AffineSpace n S ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (AffineSpace n S ↘ S) fun i =>
    AffineSpace.coord S i - AffineSpace.coord S i ^ p

/-- The endomorphism with coordinates `xᵢ - xᵢ ^ p` commutes with the morphism of affine
spaces induced by a morphism of base schemes. -/
lemma affineSpace_map_comm_subPow
    {S T : Scheme.{u}} {n : Type u}
    (f : S ⟶ T) (p : ℕ) :
    AffineSpace.map n f ≫ affineSpaceSubPow p =
      affineSpaceSubPow p ≫ AffineSpace.map n f := by
  apply AffineSpace.hom_ext
  · simp [affineSpaceSubPow, AffineSpace.map_over, Category.assoc]
  · intro i
    show (AffineSpace.map n f).appTop
        ((affineSpaceSubPow p).appTop (AffineSpace.coord T i)) =
      (affineSpaceSubPow p).appTop
        ((AffineSpace.map n f).appTop (AffineSpace.coord T i))
    simp [affineSpaceSubPow, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.map_appTop_coord]

/-- The fibre of affine space over a point of the base is affine space over the residue
field of that point. -/
noncomputable def affineSpace_fiberIso
    {X : Scheme.{u}} (x : X) (n : Type u) :
    AffineSpace n (Spec (X.residueField x)) ≅
      (AffineSpace n X ↘ X).fiber x :=
  (AffineSpace.isPullback_map (n := n) (X.fromSpecResidueField x)).isoPullback

/-- A bijection of index types induces an isomorphism of affine spaces over `S`. -/
noncomputable def affineSpace_reindexIso
    {S : Scheme.{u}} {n m : Type u} (e : n ≃ m) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex e.symm S
  inv := AffineSpace.reindex e S
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      change (AffineSpace.reindex e.symm S).appTop
          ((AffineSpace.reindex e S).appTop (AffineSpace.coord S i)) = _
      simp [AffineSpace.reindex_appTop_coord]
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      change (AffineSpace.reindex e S).appTop
          ((AffineSpace.reindex e.symm S).appTop (AffineSpace.coord S i)) = _
      simp [AffineSpace.reindex_appTop_coord]

/-- The elementary coordinate shear on the polynomial ring indexed by `ULift (Fin d)`. -/
noncomputable def coordinateShearULift
    {R : Type*} [CommRing R] {d : ℕ}
    (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
    MvPolynomial (ULift.{u} (Fin d)) R ≃ₐ[R]
      MvPolynomial (ULift.{u} (Fin d)) R := by
  let e := MvPolynomial.renameEquiv R
    (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  exact e.trans ((MvPolynomial.coordinateShear i j hij r).trans e.symm)

/-- The shear `coordinateShearULift i j hij r` sends the `i`-th variable to
`Xᵢ + Xⱼ ^ r`. -/
lemma coordinateShearULift_apply_X
    {R : Type*} [CommRing R] {d : ℕ}
    (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
    coordinateShearULift (R := R) (d := d) i j hij r
        (MvPolynomial.X (ULift.up i)) =
      MvPolynomial.X (ULift.up i) + MvPolynomial.X (ULift.up j) ^ r := by
  simp [coordinateShearULift, MvPolynomial.coordinateShear,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

/-- If `φ ∘ ρ = ρ ∘ ψ` and a subset `W` of `Spec A` is invariant under `Spec ψ`, then its
pullback along `Spec ρ` is invariant under `Spec φ`. -/
private lemma preimage_comap_invariant_of_comp_eq
    {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B) (φ : B →+* B) (ψ : A →+* A)
    (hconj : φ.comp ρ = ρ.comp ψ) (W : Set (PrimeSpectrum A))
    (h : PrimeSpectrum.comap ψ ⁻¹' W = W) :
    PrimeSpectrum.comap φ ⁻¹' (PrimeSpectrum.comap ρ ⁻¹' W) = PrimeSpectrum.comap ρ ⁻¹' W := by
  ext q
  show PrimeSpectrum.comap ρ (PrimeSpectrum.comap φ q) ∈ W ↔ PrimeSpectrum.comap ρ q ∈ W
  have hp : PrimeSpectrum.comap ρ (PrimeSpectrum.comap φ q) =
      PrimeSpectrum.comap ψ (PrimeSpectrum.comap ρ q) := by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hconj]
  rw [hp]
  exact Set.ext_iff.mp h _

/-- A nonempty open subset of affine `d`-space on the index type `ULift (Fin d)`, `d ≥ 2`,
invariant under the coordinate shears and, in positive characteristic, under
`Xᵢ ↦ Xᵢ - Xᵢ ^ p`, is everything. -/
lemma affineOpen_eq_univ_of_shear_and_sub_pow_invariant_ulift
    {k : Type u} [Field k] (d : ℕ) (hd : 2 ≤ d)
    (W : Set (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin d)) k)))
    (hopen : IsOpen W) (hnonempty : W.Nonempty)
    (hWinv : ∀ (i j : Fin d) (hij : i ≠ j) (r : ℕ),
      PrimeSpectrum.comap
        (coordinateShearULift (R := k) i j hij r).toRingHom ⁻¹' W = W)
    (hfrob : 0 < ringChar k → PrimeSpectrum.comap
      (MvPolynomial.aeval (R := k) (fun i : ULift.{u} (Fin d) =>
        MvPolynomial.X i - MvPolynomial.X i ^ ringChar k)).toRingHom ⁻¹' W = W) :
    W = Set.univ := by
  classical
  let ρ := MvPolynomial.renameEquiv k
    (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  let H := PrimeSpectrum.homeomorphOfRingEquiv ρ.toRingEquiv
  let Wfin : Set (PrimeSpectrum (MvPolynomial (Fin d) k)) := H.symm ⁻¹' W
  have hopenfin : IsOpen Wfin := hopen.preimage H.symm.continuous
  have hnonemptyfin : Wfin.Nonempty := by
    obtain ⟨q, hq⟩ := hnonempty
    exact ⟨H q, by simpa [Wfin, H] using hq⟩
  have hconj (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
      (MvPolynomial.coordinateShear (R := k) i j hij r).toRingHom.comp ρ.toRingHom =
        ρ.toRingHom.comp
          (coordinateShearULift (R := k) i j hij r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ρ, coordinateShearULift, MvPolynomial.coordinateShear]
    · intro l
      by_cases hl : l.down = i <;> simp [ρ, coordinateShearULift, MvPolynomial.coordinateShear, hl]
  have hWinvfin : ∀ (i j : Fin d) (hij : i ≠ j) (r : ℕ),
      PrimeSpectrum.comap
        (MvPolynomial.coordinateShear (R := k) i j hij r).toRingHom ⁻¹' Wfin = Wfin :=
    fun i j hij r => preimage_comap_invariant_of_comp_eq ρ.toRingHom _ _ (hconj i j hij r) W
      (hWinv i j hij r)
  have hfrobfin : 0 < ringChar k → PrimeSpectrum.comap
      (MvPolynomial.aeval (R := k) (fun i : Fin d =>
        MvPolynomial.X i - MvPolynomial.X i ^ ringChar k)).toRingHom ⁻¹' Wfin = Wfin := by
    intro hchar
    refine preimage_comap_invariant_of_comp_eq ρ.toRingHom _ _ ?_ W (hfrob hchar)
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [ρ]
  have hfull := affineOpen_eq_univ_of_shear_and_sub_pow_invariant
    hd Wfin hopenfin hnonemptyfin hWinvfin hfrobfin
  ext q
  have hq : H q ∈ Wfin := by rw [hfull]; simp
  simpa [Wfin, H] using hq

/-- On global sections, `Spec.map φ` acts as `φ` itself under the canonical identification
of `Γ(Spec R, ⊤)` with `R`. -/
lemma specMap_appTop_ΓSpecIso_inv_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : S →+* R) (a : S) :
    (Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (.of S)).inv a) =
      (Scheme.ΓSpecIso (.of R)).inv (φ a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h' := congrArg
    (fun f : CommRingCat.of S ⟶ Γ(Spec (.of R), ⊤) => (ConcreteCategory.hom f) a) h
  change (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of R)).inv).hom a =
      ((Scheme.ΓSpecIso (.of S)).inv ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop).hom a at h'
  rw [CommRingCat.comp_apply] at h'
  exact h'.symm

/-- The endomorphism with coordinates `xᵢ - xᵢ ^ p` is compatible with the canonical
morphism from affine space to the spectrum of the integral polynomial ring. -/
lemma affineSpace_subPow_toSpecMvPoly
    {S : Scheme.{u}} {n : Type u} (p : ℕ) :
    affineSpaceSubPow p ≫ AffineSpace.toSpecMvPoly n S =
      AffineSpace.toSpecMvPoly n S ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ULift.{u} ℤ)
          (fun i : n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv n).injective
  funext i
  show (affineSpaceSubPow p).appTop (AffineSpace.coord S i) =
    (AffineSpace.toSpecMvPoly n S).appTop
      ((Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ULift.{u} ℤ)
        (fun i : n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)).appTop
          ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i)))
  rw [specMap_appTop_ΓSpecIso_inv_apply]
  simp only [affineSpaceSubPow, AffineSpace.homOfVector_appTop_coord]
  simp [AffineSpace.coord, AffineSpace.toSpecMvPolyIntEquiv]

/-- The endomorphism with coordinates `xᵢ - xᵢ ^ p` is the base change of the corresponding
endomorphism of the spectrum of the integral polynomial ring. -/
lemma affineSpace_subPow_isPullback
    {S : Scheme.{u}} {n : Type u} (p : ℕ) :
    IsPullback (affineSpaceSubPow p) (AffineSpace.toSpecMvPoly n S)
      (AffineSpace.toSpecMvPoly n S)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ULift.{u} ℤ)
        (fun i : n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom)) := by
  have h : IsPullback (AffineSpace n S ↘ S) (AffineSpace.toSpecMvPoly n S)
      (terminal.from S) (terminal.from _) := IsPullback.of_hasPullback _ _
  apply IsPullback.of_right _ (affineSpace_subPow_toSpecMvPoly p) h
  simpa [affineSpaceSubPow] using h

/-- The endomorphism with coordinates `xᵢ - xᵢ ^ p` is étale at a point of affine space
whose image has residue field of characteristic dividing `p`. -/
lemma affineSpace_subPow_etaleAt
    {S : Scheme.{u}} (n p : ℕ) (z : AffineSpace (ULift.{u} (Fin n)) S)
    (hp : (p : S.residueField ((AffineSpace (ULift.{u} (Fin n)) S ↘ S) z)) = 0) :
    EtaleAt (affineSpaceSubPow p) z := by
  let a := AffineSpace.toSpecMvPoly (ULift.{u} (Fin n)) S
  let q := a z
  have hz : (p : (AffineSpace (ULift.{u} (Fin n)) S).residueField z) = 0 := by
    simpa using congrArg ((AffineSpace (ULift.{u} (Fin n)) S ↘ S).residueFieldMap z).hom hp
  have hq : (p : (Spec (.of (MvPolynomial (ULift.{u} (Fin n))
      (ULift.{u} ℤ)))).residueField q) = 0 := by
    apply (a.residueFieldMap z).hom.injective
    simpa using hz
  apply etaleAt_of_isPullback (affineSpace_subPow_isPullback p).flip z
  apply spec_sub_pow_etaleAt_ulift
  let : q.asIdeal.IsPrime := q.isPrime
  apply Ideal.algebraMap_residueField_eq_zero.mp
  simpa using congrArg (Scheme.Spec.residueFieldIso _ q).hom.hom hq

/-- Under the identification of affine space over `Spec k` with the spectrum of a polynomial
ring, an elementary coordinate shear corresponds to `coordinateShearULift`. -/
lemma affineSpace_fiberSpecIso_inv_shear
    (k : CommRingCat.{u}) (d : ℕ)
    (i j : Fin d) (hij : i ≠ j) (r : ℕ) :
      Spec.map (CommRingCat.ofHom
        (coordinateShearULift (R := k) i j hij r).toRingHom) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin d)) k).inv =
      (AffineSpace.SpecIso (ULift.{u} (Fin d)) k).inv ≫
        affineSpaceCoordinateShear (ULift.up i) (ULift.up j)
          (by intro h; exact hij (congrArg ULift.down h)) r := by
  apply AffineSpace.hom_ext
  · let e := AffineSpace.SpecIso (ULift.{u} (Fin d)) k
    let q := (AffineSpace (ULift.{u} (Fin d)) (Spec k) ↘ Spec k)
    let α : MvPolynomial (ULift.{u} (Fin d)) k →+*
        MvPolynomial (ULift.{u} (Fin d)) k :=
      (coordinateShearULift (R := k) (d := d) i j hij r).toRingHom
    let s : AffineSpace (ULift.{u} (Fin d)) (Spec k) ⟶
        AffineSpace (ULift.{u} (Fin d)) (Spec k) :=
      affineSpaceCoordinateShear (ULift.up i) (ULift.up j)
        (by intro h; exact hij (congrArg ULift.down h)) r
    show Spec.map (CommRingCat.ofHom α) ≫ e.inv ≫ q = e.inv ≫ s ≫ q
    calc
      Spec.map (CommRingCat.ofHom α) ≫ e.inv ≫ q =
          Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
            dsimp [e]
            rw [AffineSpace.SpecIso_inv_over]
      _ = Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have hC : α.comp (MvPolynomial.C : k →+*
            MvPolynomial (ULift.{u} (Fin d)) k) =
            MvPolynomial.C := RingHom.ext fun a =>
          (coordinateShearULift (R := k) (d := d) i j hij r).commutes a
        rw [hC]
      _ = e.inv ≫ q := by
        dsimp [e]
        rw [AffineSpace.SpecIso_inv_over]
      _ = e.inv ≫ s ≫ q := by
        symm
        dsimp [s, affineSpaceCoordinateShear]
        rw [AffineSpace.homOfVector_over]
  · intro l
    let e := AffineSpace.SpecIso (ULift.{u} (Fin d)) k
    let α : MvPolynomial (ULift.{u} (Fin d)) k →+*
        MvPolynomial (ULift.{u} (Fin d)) k :=
      (coordinateShearULift (R := k) (d := d) i j hij r).toRingHom
    let s : AffineSpace (ULift.{u} (Fin d)) (Spec k) ⟶
        AffineSpace (ULift.{u} (Fin d)) (Spec k) :=
      affineSpaceCoordinateShear (ULift.up i) (ULift.up j)
        (by intro h; exact hij (congrArg ULift.down h)) r
    show (Spec.map (CommRingCat.ofHom α)).appTop (e.inv.appTop (AffineSpace.coord (Spec k) l)) =
      e.inv.appTop (s.appTop (AffineSpace.coord (Spec k) l))
    rw [AffineSpace.SpecIso_inv_appTop_coord, specMap_appTop_ΓSpecIso_inv_apply]
    by_cases hl : l = ULift.up i
    · subst l
      show (Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin d)) k))).inv
          ((coordinateShearULift (R := k) (d := d)
            i j hij r) (MvPolynomial.X (ULift.up i))) = _
      rw [coordinateShearULift_apply_X (R := k)
        (d := d) i j hij r]
      have hs : s.appTop (AffineSpace.coord (Spec k) (ULift.up i)) =
          AffineSpace.coord (Spec k) (ULift.up i) +
            AffineSpace.coord (Spec k) (ULift.up j) ^ r := by
        simp [s, affineSpaceCoordinateShear, AffineSpace.homOfVector_appTop_coord]
      rw [hs]
      simp [e, AffineSpace.SpecIso_inv_appTop_coord, map_add, map_pow]
    · have hdown : l.down ≠ i := by
        intro h
        exact hl (ULift.ext (x := l) (y := ULift.up i) h)
      have hα : α (MvPolynomial.X l) = MvPolynomial.X l := by
        show ((MvPolynomial.renameEquiv _
          (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)).trans
          ((MvPolynomial.coordinateShear i j hij r).trans
            (MvPolynomial.renameEquiv _
              (Equiv.ulift.symm : Fin d ≃ ULift.{u} (Fin d)))))
          (MvPolynomial.X l) = MvPolynomial.X l
        simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
          MvPolynomial.rename_X]
        simp [MvPolynomial.coordinateShear, hdown]
      rw [hα]
      simp [e, s, affineSpaceCoordinateShear, hl,
        AffineSpace.homOfVector_appTop_coord]

/-- Under the identification of affine space over `Spec R` with the spectrum of a polynomial
ring, the endomorphism with coordinates `xᵢ - xᵢ ^ p` corresponds to `Xᵢ ↦ Xᵢ - Xᵢ ^ p`. -/
lemma affineSpace_specIso_inv_sub_pow
    (R : CommRingCat.{u}) (n : Type u) (p : ℕ) :
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := R)
        (fun i : n => MvPolynomial.X i - MvPolynomial.X i ^ p)).toRingHom) ≫
        (AffineSpace.SpecIso n R).inv =
      (AffineSpace.SpecIso n R).inv ≫ affineSpaceSubPow p := by
  let φ : MvPolynomial n R →ₐ[R] MvPolynomial n R := MvPolynomial.aeval
    (fun i : n => MvPolynomial.X i - MvPolynomial.X i ^ p)
  apply AffineSpace.hom_ext
  · show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (AffineSpace.SpecIso n R).inv ≫
        (AffineSpace n (Spec R) ↘ Spec R) =
      (AffineSpace.SpecIso n R).inv ≫ affineSpaceSubPow p ≫
        (AffineSpace n (Spec R) ↘ Spec R)
    simp only [affineSpaceSubPow, AffineSpace.homOfVector_over,
      AffineSpace.SpecIso_inv_over]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => φ.commutes r
  · intro i
    show (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop
        ((AffineSpace.SpecIso n R).inv.appTop (AffineSpace.coord (Spec R) i)) =
      (AffineSpace.SpecIso n R).inv.appTop
        ((affineSpaceSubPow p).appTop (AffineSpace.coord (Spec R) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, specMap_appTop_ΓSpecIso_inv_apply]
    simp [φ, affineSpaceSubPow, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.SpecIso_inv_appTop_coord]

/-- The identification of the fibre of affine space with affine space over the residue field
is compatible with the inclusion of the fibre. -/
lemma affineSpace_fiberIso_hom_fiberι
    {X : Scheme.{u}} (x : X) (n : Type u) :
    (affineSpace_fiberIso x n).hom ≫
        (AffineSpace n X ↘ X).fiberι x =
      AffineSpace.map n (X.fromSpecResidueField x) :=
  (AffineSpace.isPullback_map (n := n) (X.fromSpecResidueField x)).isoPullback_hom_fst

/-- Every point of affine space over `X` is the image of a point of affine space over the
residue field of its image in `X`. -/
lemma affineSpace_exists_fiber_point
    {X : Scheme.{u}} {n : Type u} (z : AffineSpace n X) :
    ∃ w : AffineSpace n (Spec (X.residueField ((AffineSpace n X ↘ X) z))),
      (AffineSpace.map n (X.fromSpecResidueField ((AffineSpace n X ↘ X) z))) w = z := by
  let x := (AffineSpace n X ↘ X) z
  let q := ((AffineSpace n X ↘ X).fiberHomeo x).symm ⟨z, rfl⟩
  refine ⟨(affineSpace_fiberIso x n).inv q, ?_⟩
  rw [← affineSpace_fiberIso_hom_fiberι]
  show (AffineSpace n X ↘ X).fiberι x
    ((affineSpace_fiberIso x n).hom ((affineSpace_fiberIso x n).inv q)) = z
  have he : (affineSpace_fiberIso x n).hom ((affineSpace_fiberIso x n).inv q) = q :=
    congrArg (fun f => f q) (affineSpace_fiberIso x n).inv_hom_id
  rw [he]
  exact Scheme.Hom.fiberι_fiberHomeo_symm _ _ ⟨z, rfl⟩

/-- Affine space on a finite index type is smooth over its base. -/
lemma affineSpace_smooth_over {S : Scheme.{u}} {n : Type u} [Finite n] :
    Smooth (AffineSpace n S ↘ S) := by
  let _fin : Fintype n := Fintype.ofFinite n
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@Smooth : MorphismProperty Scheme.{u})
      (terminal.from S) :=
    ⟨fun pb hg => AlgebraicGeometry.smooth_isStableUnderBaseChange.of_isPullback pb hg⟩
  let : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.pullback_fst (P := @Smooth)
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal
    (terminal.from (Spec (.of (ULift.{u} ℤ))))
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom (MvPolynomial.C :
    ULift.{u} ℤ →+* MvPolynomial n (ULift.{u} ℤ)))),
    MorphismProperty.cancel_right_of_respectsIso (P := @Smooth),
    HasRingHomProperty.Spec_iff (P := @Smooth), RingHom.Smooth]
  convert! ({} : Algebra.Smooth (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ)))
  exact Algebra.algebra_ext _ _ fun _ => rfl

/-- Affine space on a sum of two index types is affine space on the second factor over affine
space on the first. -/
noncomputable def affineSpaceSumIso
    (n m : Type u) (S : Scheme.{u}) :
    AffineSpace (n ⊕ m) S ≅ AffineSpace m (AffineSpace n S) where
  hom := AffineSpace.homOfVector (AffineSpace.reindex Sum.inl S)
    (fun j => AffineSpace.coord S (Sum.inr j))
  inv := AffineSpace.homOfVector
    ((AffineSpace m (AffineSpace n S) ↘ AffineSpace n S) ≫ (AffineSpace n S ↘ S))
    (Sum.elim (fun i => (AffineSpace m (AffineSpace n S) ↘ AffineSpace n S).appTop
      (AffineSpace.coord S i)) (fun j => AffineSpace.coord (AffineSpace n S) j))
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.homOfVector_over, Category.id_comp]
      rw [← Category.assoc, AffineSpace.homOfVector_over, AffineSpace.reindex_over]
    · intro i
      cases i with
      | inl i =>
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Sum.elim_inl]
        change ((AffineSpace.homOfVector (AffineSpace.reindex Sum.inl S)
          (fun j : m => AffineSpace.coord S (Sum.inr j))) ≫
            (AffineSpace m (AffineSpace n S) ↘ AffineSpace n S)).appTop
              (AffineSpace.coord S i) = _
        rw [AffineSpace.homOfVector_over, AffineSpace.reindex_appTop_coord]
        simp
      | inr j =>
        rw [Scheme.Hom.comp_appTop]
        simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · apply AffineSpace.hom_ext
      · simp
      · intro i
        rw [Scheme.Hom.comp_appTop]
        simp only [Category.id_comp, CommRingCat.comp_apply]
        rw [Scheme.Hom.comp_appTop]
        simp only [CommRingCat.comp_apply]
        conv_lhs => arg 2; rw [← CommRingCat.comp_apply]
        rw [← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
          AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord]
        rfl
    · intro j
      rw [Scheme.Hom.comp_appTop]
      simp

/-- Affine `(d + 2)`-space over `S` is affine `2`-space over affine `d`-space over `S`. -/
noncomputable def affineSpaceAddTwoIso (d : ℕ) (S : Scheme.{u}) :
    AffineSpace (ULift.{u} (Fin (d + 2))) S ≅
      AffineSpace (ULift.{u} (Fin 2)) (AffineSpace (ULift.{u} (Fin d)) S) :=
  (affineSpace_reindexIso
    (Equiv.ulift.trans (finSumFinEquiv.symm.trans
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm)))).trans
    (affineSpaceSumIso _ _ S)

/-- The identification of affine `(d + 2)`-space with affine `2`-space over affine `d`-space
turns the projection into the reindexing along the first `d` coordinates. -/
lemma affineSpaceAddTwoIso_hom_over (d : ℕ) (S : Scheme.{u}) :
    (affineSpaceAddTwoIso d S).hom ≫
      (AffineSpace (ULift.{u} (Fin 2)) (AffineSpace (ULift.{u} (Fin d)) S) ↘
        AffineSpace (ULift.{u} (Fin d)) S) =
      AffineSpace.reindex (fun i : ULift.{u} (Fin d) => ULift.up (Fin.castAdd 2 i.down)) S := by
  dsimp [affineSpaceAddTwoIso, affineSpaceSumIso, affineSpace_reindexIso]
  rw [Category.assoc, AffineSpace.homOfVector_over]
  apply AffineSpace.hom_ext
  · simp
  · intro i
    rw [Scheme.Hom.comp_appTop]
    simp [AffineSpace.reindex_appTop_coord]

/-- A morphism smooth at a point is smooth after restricting its source to a suitable open
neighbourhood of that point. -/
lemma smoothAt_has_smooth_open_neighborhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : InfinitesimalLifting.SmoothAt f x) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  obtain ⟨U, V, hU, hV, hxU, hUV, happ⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine f x).mp hf
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : Smooth (f.resLE V U hUV) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2 <|
      (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V U hUV)).mpr happ
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hUV]
  infer_instance

end AlgebraicGeometry

end

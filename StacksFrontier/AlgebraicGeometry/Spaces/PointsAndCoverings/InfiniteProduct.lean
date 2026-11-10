module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Topology.Separation.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# The infinite product example

Fix a commutative ring `k`, put `S = Spec k` and let `U` be the spectrum of the countable
product `∏ n : ℕ, k`. The coordinate projections give morphisms `S ⟶ U` over `S`, and the
scheme `R = U ⨿ ∐_{n ≠ m} S` carries a canonical morphism to `U ×_S U` which is the
identity relation on the distinguished summand and the pair of coordinate points on the
summand indexed by `(n, m)`. This is the data from which the source builds an algebraic
space that is not a scheme.

The source's analysis of this example when `k` is a finite field is recorded here as well:
every element of the product ring satisfies the finite-field power identity, the residue
field at every prime of the product is `k` again, every point of `U` is closed, and the
coordinate points are dense in `U`.

## Main definitions

* `AlgebraicGeometry.Space.InfiniteProduct.productRing`,
  `AlgebraicGeometry.Space.InfiniteProduct.base` and
  `AlgebraicGeometry.Space.InfiniteProduct.space` are the ring `∏ n : ℕ, k` and the schemes
  `S` and `U`.
* `AlgebraicGeometry.Space.InfiniteProduct.structureMap` and
  `AlgebraicGeometry.Space.InfiniteProduct.coordinate` are the structure morphism `U ⟶ S`
  and the morphism `S ⟶ U` induced by a coordinate projection.
* `AlgebraicGeometry.Space.InfiniteProduct.relation` is the scheme `R` and
  `AlgebraicGeometry.Space.InfiniteProduct.relationMap` its morphism to `U ×_S U`.

## Main results

* `AlgebraicGeometry.Space.InfiniteProduct.coordinate_comp_structureMap`: every coordinate
  morphism is a section of the structure morphism.
* `AlgebraicGeometry.Space.InfiniteProduct.relation_ι_relationMap`: the restriction of
  `relationMap` to a summand is its specified component.
* `AlgebraicGeometry.Space.InfiniteProduct.pow_card_eq_self`,
  `AlgebraicGeometry.Space.InfiniteProduct.nonempty_algEquiv_residueField` and
  `AlgebraicGeometry.Space.InfiniteProduct.isClosed_singleton`: the power identity in the
  product of a finite field, the identification of each of its residue fields with that
  field, and closedness of every point of `U`.
* `AlgebraicGeometry.Space.InfiniteProduct.dense_coordinatePoints`: the coordinate points
  are dense in `U`.
* `AlgebraicGeometry.Space.InfiniteProduct.exists_unit_mul_idempotent`,
  `AlgebraicGeometry.Space.InfiniteProduct.isTopologicalBasis_isClopen` and
  `AlgebraicGeometry.Space.InfiniteProduct.instTotallyDisconnectedSpace`: every element of the
  product ring is a unit times an idempotent, so the clopen subsets of `U` form a topological
  basis and `U` is totally disconnected.
* `AlgebraicGeometry.Space.InfiniteProduct.isOpen_singleton_iff_coordinate`,
  `AlgebraicGeometry.Space.InfiniteProduct.exists_noncoordinate_point` and
  `AlgebraicGeometry.Space.InfiniteProduct.not_discreteTopology`: the open points of `U` are
  exactly the coordinate points, there are other points, and `U` is not discrete.

## Implementation notes

The disjoint union `R` is one indexed coproduct whose index type is the sum of a singleton
and the subtype of off-diagonal ordered pairs of natural numbers, which is canonically the
displayed coproduct of the source. The definitions are exposed so that clients use the
coproduct and pullback computation rules directly rather than through transport lemmas.

The cardinal `q` of the source is `Nat.card k`. Finiteness of each residue field is derived
from the power identity rather than from finiteness of the product ring, which is not
finite: an integral domain in which `x ^ q = x` holds identically embeds into the root set
of `X ^ q - X`, hence has at most `q` elements, and a finite domain is a field. The
`k`-algebra equivalence with the residue field then comes from injectivity of the structure
map together with that cardinality bound.

Closedness of a point of `U` is closedness of the corresponding prime of the product ring,
which holds because that prime is maximal, transported along the canonical isomorphism of
`U` with the spectrum of its ring of global sections.

Density of the coordinate points is proved for an arbitrary field; the source invokes it
only for a finite field.

## References

* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.InfiniteProduct

variable (k : Type u) [CommRing k]

/-- The countable product of copies of `k`. -/
abbrev productRing := ℕ → k

/-- The base scheme `Spec(k)`. -/
noncomputable abbrev base : Scheme.{u} := Spec (.of k)

/-- The spectrum of the countable product of copies of `k`. -/
noncomputable abbrev space : Scheme.{u} := Spec (.of (productRing k))

/-- The structure morphism from the spectrum of the product to `Spec(k)`, induced by the
diagonal homomorphism from `k` to its countable product. -/
@[implicit_reducible]
noncomputable def structureMap : space k ⟶ base k :=
  Spec.map (CommRingCat.ofHom (Pi.constRingHom ℕ k))

/-- The morphism `Spec(k) ⟶ Spec(∏ _ : ℕ, k)` induced by evaluation at `n`. -/
@[implicit_reducible]
noncomputable def coordinate (n : ℕ) : base k ⟶ space k :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ℕ ↦ k) n))

/-- A coordinate morphism followed by the structure morphism is the identity of
`Spec(k)`. -/
@[simp]
lemma coordinate_comp_structureMap (n : ℕ) :
    coordinate k n ≫ structureMap k = 𝟙 (base k) := by
  unfold coordinate structureMap
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- Ordered pairs of distinct natural numbers. -/
abbrev OffDiagonal := { p : ℕ × ℕ // p.1 ≠ p.2 }

/-- The indexing type for the summands of the relation: one distinguished copy of `U`,
followed by a copy of `S` for every off-diagonal ordered pair. -/
abbrev RelationIndex := Unit ⊕ OffDiagonal

/-- The family whose coproduct is the relation scheme. -/
noncomputable abbrev relationComponent : RelationIndex → Scheme.{u}
  | .inl _ => space k
  | .inr _ => base k

/-- The relation scheme `U ⨿ ∐ _ : {p : ℕ × ℕ // p.1 ≠ p.2}, S`. -/
noncomputable abbrev relation : Scheme.{u} := ∐ relationComponent k

/-- On the distinguished summand this is the diagonal of `U` over `S`; on the summand
indexed by `(n, m)` it is the morphism to the pullback with components `coordinate k n` and
`coordinate k m`. -/
@[implicit_reducible]
noncomputable def relationComponentMap : (i : RelationIndex) →
    relationComponent k i ⟶ pullback (structureMap k) (structureMap k)
  | .inl _ => pullback.diagonal (structureMap k)
  | .inr p => pullback.lift (coordinate k p.1.1) (coordinate k p.1.2)
      ((coordinate_comp_structureMap k p.1.1).trans
        (coordinate_comp_structureMap k p.1.2).symm)

/-- The morphism from the relation scheme to `U ×_S U`. -/
@[implicit_reducible]
noncomputable def relationMap : relation k ⟶ pullback (structureMap k) (structureMap k) :=
  Sigma.desc (relationComponentMap k)

/-- The restriction of `relationMap` to a summand is its specified component map. -/
@[reassoc (attr := simp)]
lemma relation_ι_relationMap (i : RelationIndex) :
    Sigma.ι (relationComponent k) i ≫ relationMap k = relationComponentMap k i := by
  simp [relationMap]

/-! ### The product of a finite field -/

section FiniteField

variable (K : Type u) [Field K] [Finite K]

/-- **Stacks Project, Tag 02Z8.** Every element of the product of copies of a finite field
satisfies `x ^ q = x`, where `q` is the number of elements of the field. -/
@[stacks 02Z8 "residue_fields_and_closed_points"]
theorem pow_card_eq_self (x : productRing K) : x ^ Nat.card K = x := by
  let _ : Fintype K := Fintype.ofFinite K
  funext n
  change x n ^ Nat.card K = x n
  simpa only [Nat.card_eq_fintype_card] using (FiniteField.pow_card (x n))

/-- The power identity passes to the quotient by a prime of the product. -/
private theorem quotient_pow_card_eq_self (p : PrimeSpectrum (productRing K))
    (x : productRing K ⧸ p.asIdeal) : x ^ Nat.card K = x := by
  induction x using Quotient.inductionOn' with
  | _ x => exact congrArg (Ideal.Quotient.mk p.asIdeal) (pow_card_eq_self K x)

/-- An integral domain in which `x ^ q = x` holds identically, for some `q > 1`, is finite
with at most `q` elements: every element is a root of `X ^ q - X`. -/
private theorem finite_of_pow_card_eq_self {R : Type*} [CommRing R] [IsDomain R]
    (q : ℕ) (hq : 1 < q) (hpow : ∀ x : R, x ^ q = x) :
    Finite R ∧ Nat.card R ≤ q := by
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.X
  have hdeg : P.natDegree = q := by
    dsimp only [P]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow _
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      exact hq
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hdeg]; omega)
  have hroot : ∀ x : R, P.IsRoot x := by
    intro x
    change Polynomial.eval x P = 0
    simp [P, hpow x]
  have : Finite {x : R // P.IsRoot x} := (Polynomial.finite_setOfPred_isRoot hP).to_subtype
  have hfinite : Finite R :=
    Finite.of_injective (fun x : R => ⟨x, hroot x⟩) fun _ _ h => congrArg Subtype.val h
  have hroots : P.rootSet R = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    exact (Polynomial.mem_rootSet).2 ⟨hP, by simpa [Polynomial.IsRoot] using hroot x⟩
  have hcard := Polynomial.ncard_rootSet_le P R
  rw [hroots, Set.ncard_univ, hdeg] at hcard
  exact ⟨hfinite, hcard⟩

/-- Every prime of the product of copies of a finite field has a quotient which is a
field. -/
private theorem quotient_isField (p : PrimeSpectrum (productRing K)) :
    IsField (productRing K ⧸ p.asIdeal) := by
  have : Finite (productRing K ⧸ p.asIdeal) :=
    (finite_of_pow_card_eq_self _ (Finite.one_lt_card) (quotient_pow_card_eq_self K p)).1
  exact Finite.isField_of_domain _

/-- The quotient of the product by a prime is `K` again, as a `K`-algebra. -/
private noncomputable def quotient_algEquiv (p : PrimeSpectrum (productRing K)) :
    K ≃ₐ[K] productRing K ⧸ p.asIdeal := by
  let Q := productRing K ⧸ p.asIdeal
  have hcardQ := finite_of_pow_card_eq_self _ (Finite.one_lt_card) (quotient_pow_card_eq_self K p)
  have : Finite Q := hcardQ.1
  exact AlgEquiv.ofBijective (Algebra.ofId K Q)
    ((FaithfulSMul.algebraMap_injective K Q).bijective_of_nat_card_le hcardQ.2)

/-- **Stacks Project, Tag 02Z8.** The residue field at any prime of the product is
isomorphic to the factor field, compatibly with its diagonal `K`-algebra structure. -/
@[stacks 02Z8 "residue_fields_and_closed_points"]
theorem nonempty_algEquiv_residueField (p : PrimeSpectrum (productRing K)) :
    Nonempty (K ≃ₐ[K] p.asIdeal.ResidueField) := by
  let Q := productRing K ⧸ p.asIdeal
  have : p.asIdeal.IsMaximal := Ideal.Quotient.maximal_of_isField _ (quotient_isField K p)
  let e : Q ≃ₐ[Q] p.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId Q _)
      (Ideal.bijective_algebraMap_quotient_residueField p.asIdeal)
  exact ⟨(quotient_algEquiv K p).trans (e.restrictScalars K)⟩

/-- **Stacks Project, Tag 02Z8.** Every point of the spectrum of the product of copies of a
finite field is closed. -/
@[stacks 02Z8 "residue_fields_and_closed_points"]
theorem isClosed_singleton (x : space K) : IsClosed ({x} : Set (space K)) := by
  let e : Γ(space K, ⊤) ≃+* productRing K :=
    (Scheme.ΓSpecIso (.of (productRing K))).commRingCatIsoToRingEquiv
  let pGamma : PrimeSpectrum Γ(space K, ⊤) := (space K).isoSpec.hom x
  let p : PrimeSpectrum (productRing K) := PrimeSpectrum.comap e.symm.toRingHom pGamma
  have hpGamma : pGamma.asIdeal.IsMaximal := by
    apply (Ideal.isMaximal_comap_iff_of_bijective e.symm.toRingHom e.symm.bijective).mp
    simpa [p, PrimeSpectrum.comap_asIdeal] using
      (Ideal.Quotient.maximal_of_isField _ (quotient_isField K p))
  rw [← show (space K).isoSpec.hom.homeomorph ⁻¹' {pGamma} = {x} by
    ext y
    change ((space K).isoSpec.hom.homeomorph y = (space K).isoSpec.hom.homeomorph x) ↔ y = x
    exact (space K).isoSpec.hom.homeomorph.injective.eq_iff]
  exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal pGamma).2 hpGamma).preimage
    (space K).isoSpec.hom.homeomorph.continuous

end FiniteField

/-- The prime of the product corresponding to a coordinate point is the kernel of the
evaluation at that coordinate. -/
private theorem asIdeal_coordinate_base_default (K : Type u) [Field K] (n : ℕ) :
    ((coordinate K n).base (default : base K)).asIdeal =
      RingHom.ker (Pi.evalRingHom (fun _ : ℕ ↦ K) n) := by
  change (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ℕ ↦ K) n)
    (default : PrimeSpectrum K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, Subsingleton.elim (default : PrimeSpectrum K) ⊥,
    PrimeSpectrum.asIdeal_bot]
  rfl

/-- **Stacks Project, Tag 02Z8.** The points of the spectrum of `∏ n : ℕ, k` determined by
the coordinate projections form a dense subset. -/
@[stacks 02Z8 "coordinate_points_dense"]
theorem dense_coordinatePoints (K : Type u) [Field K] :
    Dense (Set.range (fun n : ℕ ↦ (coordinate K n).base (default : base K))) := by
  classical
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := productRing K)).dense_iff.2 ?_
  rintro _ ⟨x, rfl⟩ ⟨p, hp⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ≠ 0 := by
    by_contra! h
    simp [show x = 0 from funext h] at hp
  refine ⟨_, ?_, ⟨n, rfl⟩⟩
  exact (PrimeSpectrum.mem_basicOpen x _).2 (by simpa [asIdeal_coordinate_base_default] using hn)

/-! ### Clopen subsets, and which points are open -/

section Clopen

variable (K : Type u) [Field K]

private theorem basicOpen_unit_mul (a : productRing K) (v : (productRing K)ˣ) :
    PrimeSpectrum.basicOpen ((v : productRing K) * a) = PrimeSpectrum.basicOpen a := by
  rw [PrimeSpectrum.basicOpen_mul]
  have h : PrimeSpectrum.basicOpen (v : productRing K) = ⊤ := by
    ext p
    simp [Ideal.notMem_of_isUnit]
  simp [h]

/-- **Stacks Project, Tag 02Z8.** Every element of a product of copies of a field is a unit
times an idempotent. -/
@[stacks 02Z8 "clopen_basis"]
theorem exists_unit_mul_idempotent (x : productRing K) :
    ∃ (u : (productRing K)ˣ) (e : productRing K),
      IsIdempotentElem e ∧ x = (u : productRing K) * e := by
  classical
  let e : productRing K := fun n ↦ if x n = 0 then 0 else 1
  let val : productRing K := fun n ↦ if x n = 0 then 1 else x n
  have hu : IsUnit val := Pi.isUnit_iff.mpr fun n ↦ by
    by_cases h : x n = 0 <;> simp [val, h, isUnit_iff_ne_zero]
  refine ⟨hu.unit, e, ?_, ?_⟩
  · change e * e = e
    funext n
    simp [e]
  · funext n
    by_cases h : x n = 0 <;> simp [e, val, h]

/-- **Stacks Project, Tag 02Z8.** The clopen subsets of the spectrum of `∏ n : ℕ, k` form a
topological basis. -/
@[stacks 02Z8 "clopen_basis"]
theorem isTopologicalBasis_isClopen :
    TopologicalSpace.IsTopologicalBasis {s : Set (space K) | IsClopen s} := by
  change TopologicalSpace.IsTopologicalBasis
    {s : Set (PrimeSpectrum (productRing K)) | IsClopen s}
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun _ ⟨_, hs⟩ ↦ hs) ?_
  intro p U hp hU
  obtain ⟨_, ⟨f, rfl⟩, hfp, hfU⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := productRing K)).mem_nhds_iff.mp
      (hU.mem_nhds hp)
  obtain ⟨v, e, he, rfl⟩ := exists_unit_mul_idempotent K f
  refine ⟨PrimeSpectrum.basicOpen e, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, ?_, ?_⟩
  · simpa [basicOpen_unit_mul] using hfp
  · simpa [basicOpen_unit_mul] using hfU

/-- **Stacks Project, Tag 02Z8.** The spectrum of `∏ n : ℕ, k` is totally disconnected. -/
@[stacks 02Z8 "clopen_basis"]
instance instTotallyDisconnectedSpace : TotallyDisconnectedSpace (space K) := by
  change TotallyDisconnectedSpace (PrimeSpectrum (productRing K))
  have : ZeroDimensionalSpace (PrimeSpectrum (productRing K)) :=
    zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr (isTopologicalBasis_isClopen K)
  infer_instance

private def finiteSupportIdeal : Ideal (productRing K) where
  carrier := {f | (Function.support f).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine (hf.union hg).subset fun n hn ↦ ?_
    simp only [Set.mem_union, Function.mem_support]
    by_contra h
    have hzero : f n = 0 ∧ g n = 0 := by simpa using h
    exact hn (by simp [hzero.1, hzero.2])
  smul_mem' := by
    intro r f hf
    refine hf.subset fun n hn ↦ ?_
    simp only [Function.mem_support]
    by_contra h
    exact hn (by simp [h])

/-- **Stacks Project, Tag 02Z8.** The open points of the spectrum of `∏ n : ℕ, k` are
precisely the points coming from the coordinate projections. -/
@[stacks 02Z8 "coordinate_and_other_points"]
theorem isOpen_singleton_iff_coordinate (x : space K) :
    IsOpen ({x} : Set (space K)) ↔
      ∃ n : ℕ, x = (coordinate K n).base (default : base K) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨_, ⟨n, rfl⟩, hyx⟩ :=
      (dense_coordinatePoints K).exists_mem_open hx (Set.singleton_nonempty x)
    exact ⟨n, (Set.mem_singleton_iff.mp hyx).symm⟩
  · rintro ⟨n, rfl⟩
    have : IsOpenImmersion (coordinate K n) :=
      AlgebraicGeometry.instIsOpenImmersionMapOfHomForallEvalRingHom n fun _ : ℕ ↦ K
    have hRange : Set.range (coordinate K n).base =
        {(coordinate K n).base (default : base K)} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      refine ⟨?_, fun h ↦ ⟨default, h.symm⟩⟩
      rintro ⟨z, rfl⟩
      exact congrArg _ (Subsingleton.elim _ _)
    rw [← hRange]
    exact (Scheme.Hom.isOpenEmbedding (coordinate K n)).isOpen_range

/-- **Stacks Project, Tag 02Z8.** The spectrum of `∏ n : ℕ, k` has a point not coming from any
coordinate projection. -/
@[stacks 02Z8 "coordinate_and_other_points"]
theorem exists_noncoordinate_point :
    ∃ x : space K, ∀ n : ℕ, x ≠ (coordinate K n).base (default : base K) := by
  classical
  have hI : finiteSupportIdeal K ≠ ⊤ := by
    intro h
    have hone : (1 : productRing K) ∈ finiteSupportIdeal K := by rw [h]; trivial
    have hfin : (Function.support (1 : productRing K)).Finite := hone
    have hsupp : Function.support (1 : productRing K) = Set.univ := by
      ext n
      simp
    rw [hsupp] at hfin
    exact Set.infinite_univ.not_finite hfin
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (finiteSupportIdeal K) hI
  refine ⟨⟨m, hm.isPrime⟩, fun n heq ↦ ?_⟩
  have hgen : Pi.single n (1 : K) ∈ m := by
    refine hIm ?_
    change (Function.support (Pi.single n (1 : K))).Finite
    exact (Set.finite_singleton n).subset (by simp)
  have hnot : Pi.single n (1 : K) ∉
      ((coordinate K n).base (default : base K)).asIdeal := by
    simp [asIdeal_coordinate_base_default]
  exact hnot (heq ▸ hgen)

/-- **Stacks Project, Tag 02Z8.** The spectrum of `∏ n : ℕ, k` is not discrete. -/
@[stacks 02Z8 "coordinate_and_other_points"]
theorem not_discreteTopology : ¬ DiscreteTopology (space K) := by
  intro hdisc
  obtain ⟨x, hx⟩ := exists_noncoordinate_point K
  obtain ⟨n, hn⟩ := (isOpen_singleton_iff_coordinate K x).mp
    (discreteTopology_iff_isOpen_singleton.mp hdisc x)
  exact hx n hn

end Clopen

end AlgebraicGeometry.Space.InfiniteProduct

end

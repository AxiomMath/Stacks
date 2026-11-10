module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.IntersectionTransversality
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The global functions on the intersection of a rational bridge with its complement

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge (Tag 0E3M). Write `X'` for
the scheme-theoretic closure of `X \ C`, and set `k' = Γ(C, 𝒪_C)` and `k'' = Γ(C ∩ X', 𝒪)`.

This file proves the assertions of [Stacks, Tag 0E3M] that `k'/k` is a finite separable extension
of fields and that `k''/k'` is either a degree two separable extension of fields or
`k'' = k' × k'`.

## Main results

* `Stacks.Curves.exists_fin_algEquiv_pi_of_etale` — a finite etale algebra over `k` is a finite
  product of finite separable extensions of any intermediate field.
* `Stacks.Curves.isField_and_isSeparable_or_algEquiv_prod_of_etale_of_finrank_eq_two` — the
  algebraic core: a finite etale algebra over `k` which is two-dimensional over an intermediate
  field `K` is either a degree two separable field extension of `K` or `K × K`.
* `Stacks.Curves.geometricallyReduced_intersection_bridge` — `C ∩ X'` is geometrically reduced
  over `k`.
* `Stacks.Curves.moduleFinite_and_isSeparable_globalSections_bridge` — `k'/k` is a finite
  separable extension of fields.
* `Stacks.Curves.isField_and_isSeparable_or_algEquiv_prod_intersectionSections_bridge` — the
  assertion of the tag on `k''/k'`.

## Implementation notes

Transversality (`Stacks.Curves.stalk_intersection_bridge_eq_maximalIdeal`) says that at a point
`x` of `C ∩ X'` the stalk of the ideal sheaf cutting the intersection out is the whole maximal
ideal of `𝒪_{X, x}`. So the local ring of `C ∩ X'` there is the residue field `κ(x)`, which is
separable over `k` because `x` is a node of `X`
(`Stacks.Curves.isSeparableExtension_residueField_of_isNode`), hence geometrically reduced over
`k` by Tag 030W. Geometric reducedness of a scheme over a field is a condition on its stalks
(Tag 035W), so `C ∩ X'` is geometrically reduced, and the global functions on a geometrically
reduced proper scheme over a field form a finite etale algebra — clauses (1), (3) and (4) of
Tag 0BUG, which is `Stacks.AlgebraicGeometry.ProperSectionsGeom`'s
`etale_globalSections_of_geometricallyReduced`.

A finite etale algebra over `k` is a product of finite separable extensions of `k`. Transporting
the `k'`-algebra structure along that decomposition makes each factor a finite extension of `k'`,
separable over `k'` because separability of an algebraic extension passes to an intermediate
field, and the degrees of the factors sum to `dim_{k'} k'' = 2`. Each factor is a field, so its
degree is at least one: either there is one factor, of degree two, or two factors, each equal to
`k'`.

The source makes the separability assertion by citing Tag 0C4D at the node `x`; that citation is
used here in the form of the separability of `κ(x)/k`, which is the clause of Tag 0C4D that
`Stacks.Curves.isSeparableExtension_residueField_of_isNode` carries.

The separability of `k'/k` comes from the same residue field: evaluation at a point of `C ∩ X'`
takes the global functions of the bridge into `κ(x)`, injectively because `k'` is a field, so
geometric reducedness over `k` descends from `κ(x)` to `k'`
(`Algebra.IsGeometricallyReduced.of_injective`) and Tag 030W reads it back as separability of
`k'/k`. Finiteness of `k'` over `k` is clause (1) of Tag 0BUG, the bridge being a closed
subscheme of `X` and hence proper over `k`; for a finite extension the separability of Tag 030O
is Mathlib's `Algebra.IsSeparable`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-! ### The algebraic core -/

/-- **A finite etale algebra over a field is a finite product of finite separable extensions of
any intermediate field.** Over the ground field this is Mathlib's description of a finite etale
algebra; the `K`-algebra structure transported along that decomposition makes each factor a
finite extension of `K`, separable over `K` because separability of an algebraic extension passes
to an intermediate field. The family is reindexed by `Fin n`. -/
@[ega "IV 18.2.3" "more general",
  ega "IV 18.3.3" "Forward direction",
  sga "1 IX 1.8" "decomposition direction",
  sga "1 XIII 2.0" "more general",
  sga "4½ Arcata 2.1.2" "partial",
  sga "4½ Arcata 2.4.2" "more general"]
theorem exists_fin_algEquiv_pi_of_etale
    (k K L : Type u) [Field k] [Field K] [CommRing L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra.Etale k L] [Module.Finite k L] :
    ∃ (n : ℕ) (Ki : Fin n → Type u) (_ : ∀ i, Field (Ki i)) (_ : ∀ i, Algebra K (Ki i)),
      (∀ i, Module.Finite K (Ki i)) ∧ (∀ i, Algebra.IsSeparable K (Ki i)) ∧
        Module.finrank K L = ∑ i, Module.finrank K (Ki i) ∧
        Nonempty (L ≃ₐ[K] (∀ i, Ki i)) := by
  classical
  obtain ⟨ι, hfinι, A, hAfield, hAalg, e, hAfinsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k L).mp inferInstance
  have := hfinι
  let := hAfield
  let := hAalg
  have : Fintype ι := Fintype.ofFinite ι
  let algKA : ∀ i, Algebra K (A i) := fun i =>
    ((Pi.evalRingHom A i).comp (e.toRingEquiv.toRingHom.comp (algebraMap K L))).toAlgebra
  have hmapA : ∀ (i : ι) (c : K), algebraMap K (A i) c = e (algebraMap K L c) i := fun i c => by
    simp only [algKA, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Pi.evalRingHom_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  let eK : L ≃ₐ[K] (∀ i, A i) :=
    { __ := e.toRingEquiv
      commutes' := fun c => funext fun i => (hmapA i c).symm }
  have htower : ∀ i, IsScalarTower k K (A i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => by
      have h1 : algebraMap k (A i) x = e (algebraMap k L x) i := by
        rw [e.commutes]
        rfl
      rw [h1, IsScalarTower.algebraMap_apply k K L x, hmapA]
  have : ∀ i, Algebra.IsSeparable k (A i) := fun i => (hAfinsep i).2
  have : ∀ i, Module.Finite k (A i) := fun i => (hAfinsep i).1
  have : ∀ i, Algebra.IsSeparable K (A i) := fun i =>
    Algebra.isSeparable_tower_top_of_isSeparable k K (A i)
  have : ∀ i, Module.Finite K (A i) := fun i => Module.Finite.of_restrictScalars_finite k K (A i)
  have : ∀ i, Module.Free K (A i) := fun i => Module.Free.of_divisionRing K (A i)
  -- reindex the finite family by `Fin (card ι)`
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Ki : Fin (Fintype.card ι) → Type u := fun i => A (eι i)
  let eP : (∀ i, Ki i) ≃ₐ[K] (∀ i, A i) := AlgEquiv.piCongrLeft K A eι
  refine ⟨Fintype.card ι, Ki, fun i => hAfield (eι i), fun i => algKA (eι i),
    fun i => inferInstanceAs (Module.Finite K (A (eι i))),
    fun i => inferInstanceAs (Algebra.IsSeparable K (A (eι i))), ?_, ⟨eK.trans eP.symm⟩⟩
  rw [eK.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype K]
  exact (Fintype.sum_equiv eι _ _ fun _ => rfl).symm

/-- **A finite etale algebra over a field which is two-dimensional over an intermediate field is
either a degree two separable field extension of it, or its square.** Decomposing the etale
algebra as a product of finite separable extensions of `K`
(`Stacks.Curves.exists_fin_algEquiv_pi_of_etale`), the degrees of the factors sum to two, and a
field factor has degree at least one: there is either one factor of degree two or two factors of
degree one. -/
@[ega "IV 18.2.3" "special case", sga "1 XIII 2.0" "special case"]
theorem isField_and_isSeparable_or_algEquiv_prod_of_etale_of_finrank_eq_two
    (k K L : Type u) [Field k] [Field K] [CommRing L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra.Etale k L] [Module.Finite k L]
    (hrank : Module.finrank K L = 2) :
    (IsField L ∧ Algebra.IsSeparable K L) ∨ Nonempty (L ≃ₐ[K] (K × K)) := by
  classical
  obtain ⟨n, Ki, hKifield, hKialg, hKifin, hKisep, hrk, ⟨eK⟩⟩ :=
    exists_fin_algEquiv_pi_of_etale k K L
  let := hKifield
  let := hKialg
  have := hKifin
  have := hKisep
  have hsum : ∑ i, Module.finrank K (Ki i) = 2 := hrk.symm.trans hrank
  have hone : ∀ i, 1 ≤ Module.finrank K (Ki i) := fun _ => Module.finrank_pos
  have hcard : (Finset.univ : Finset (Fin n)).card • 1 ≤ 2 := by
    rw [← hsum]
    exact Finset.card_nsmul_le_sum Finset.univ _ 1 fun i _ => hone i
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hcard
  have hpos : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; simp at hsum)
  obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
  · let eU : (∀ i, Ki i) ≃ₐ[K] Ki default :=
      { __ := Equiv.piUnique Ki
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    exact Or.inl ⟨MulEquiv.isField (Field.toIsField (Ki default)) (eK.trans eU).toMulEquiv,
      AlgEquiv.Algebra.isSeparable (eK.trans eU).symm⟩
  · have hsum2 : Module.finrank K (Ki 0) + Module.finrank K (Ki 1) = 2 :=
      (Fin.sum_univ_two fun i => Module.finrank K (Ki i)).symm.trans hsum
    have hrank1 : ∀ i, Module.finrank K (Ki i) = 1 := by
      have := hone 0
      have := hone 1
      exact Fin.forall_fin_two.mpr ⟨by omega, by omega⟩
    have hbijA : ∀ i, Function.Bijective (algebraMap K (Ki i)) := fun i =>
      ⟨(algebraMap K (Ki i)).injective,
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (f := Algebra.linearMap K (Ki i)) (by rw [Module.finrank_self, hrank1 i])).mp
          (algebraMap K (Ki i)).injective⟩
    let eqi : ∀ i, Ki i ≃ₐ[K] K := fun i =>
      (AlgEquiv.ofBijective (Algebra.ofId K (Ki i)) (hbijA i)).symm
    let ePair : (∀ _ : Fin 2, K) ≃ₐ[K] K × K :=
      { __ := RingEquiv.piFinTwo fun _ => K
        commutes' := fun _ => rfl }
    exact Or.inr ⟨(eK.trans (AlgEquiv.piCongrRight eqi)).trans ePair⟩

/-! ### Auxiliary facts -/

/-- The global sections map of the intersection over `k` factors through that of the bridge. -/
private theorem appTop_intersection_subschemeι_comp {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (C : X.IdealSheafData) :
    ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop =
      (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
        (Scheme.IdealSheafData.inclusion
          (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

/-- A separable field extension is geometrically reduced (Tag 030W). -/
private theorem isGeometricallyReduced_of_isSeparableExtension
    (k L : Type*) [Field k] [Field L] [Algebra k L] (h : Algebra.IsSeparableExtension k L) :
    Algebra.IsGeometricallyReduced k L :=
  ((Algebra.isSeparableExtension_tfae k L (ringExpChar k)).out 1 4).mp h

/-! ### The local rings of the intersection -/

section Bridge

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **The kernel of the stalk map of the intersection of a rational bridge with the closure of
its complement is the whole maximal ideal of the ambient local ring.** That is transversality
(`Stacks.Curves.stalk_intersection_bridge_eq_maximalIdeal`), read through the closed-immersion
computation of the stalk of a kernel ideal sheaf. -/
theorem ker_stalkMap_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    RingHom.ker ((intersectionWithComplementaryCurveIdeal C).subschemeι.stalkMap w).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk
        ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)) := by
  rw [← IdealSheafData.stalk_ker_of_isClosedImmersion
      (intersectionWithComplementaryCurveIdeal C).subschemeι w,
    Scheme.IdealSheafData.ker_subschemeι]
  exact stalk_intersection_bridge_eq_maximalIdeal hdim hnodal hC
    (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩)

/-- **The local ring of the intersection of a rational bridge with the closure of its complement
is a field.** The stalk map from the ambient local ring is surjective with kernel the whole
maximal ideal, so every element of the maximal ideal downstairs lifts to a unit and is therefore
zero. -/
theorem maximalIdeal_stalk_intersection_bridge_eq_bot
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    IsLocalRing.maximalIdeal
      ((intersectionWithComplementaryCurve C).presheaf.stalk w) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro b hb
  obtain ⟨a, ha⟩ := (intersectionWithComplementaryCurveIdeal C).subschemeι.stalkMap_surjective w b
  by_contra hb0
  have hak : a ∉ RingHom.ker
      ((intersectionWithComplementaryCurveIdeal C).subschemeι.stalkMap w).hom :=
    fun h => hb0 (ha.symm.trans h)
  rw [ker_stalkMap_intersection_bridge hdim hnodal hC w] at hak
  exact (IsLocalRing.mem_maximalIdeal b).mp hb
    (ha ▸ (IsLocalRing.notMem_maximalIdeal.mp hak).map _)

/-- **The residue field of the intersection of a rational bridge with the closure of its
complement at one of its points is separable over the base field.** The point is a node of `X`,
so the residue field of `X` there is separable over `k`
(`Stacks.Curves.isSeparableExtension_residueField_of_isNode`), and the closed immersion of the
intersection into `X` identifies the two residue fields as extensions of `k`. -/
theorem isSeparableExtension_residueField_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    letI : Algebra k ((intersectionWithComplementaryCurve C).residueField w) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
          (intersectionWithComplementaryCurve C).Γevaluation w).hom.toAlgebra
    Algebra.IsSeparableExtension k ((intersectionWithComplementaryCurve C).residueField w) := by
  have hnode : IsNode k X ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w) :=
    isNode_of_mem_intersection_bridge k X hdim hnodal C hC w
  let algX : Algebra k
      (X.residueField ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.Γevaluation ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)).hom.toAlgebra
  have hsepX : Algebra.IsSeparableExtension k
      (X.residueField ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)) :=
    isSeparableExtension_residueField_of_isNode k X hdim _ hnode
  let algW : Algebra k ((intersectionWithComplementaryCurve C).residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
        (intersectionWithComplementaryCurve C).Γevaluation w).hom.toAlgebra
  exact Algebra.IsSeparableExtension.of_algEquiv
    { __ := RingEquiv.ofBijective
        ((intersectionWithComplementaryCurveIdeal C).subschemeι.residueFieldMap w).hom
        (bijective_residueFieldMap_of_isClosedImmersion
          (intersectionWithComplementaryCurveIdeal C).subschemeι w)
      commutes' := fun r => by
        simp only [algX, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply
          (intersectionWithComplementaryCurveIdeal C).subschemeι w _ }

/-- **The intersection of a rational bridge with the closure of its complement is geometrically
reduced over the base field.** Its local ring at each point is a field, equal to its own residue
field, and that residue field is separable over `k`, hence geometrically reduced by Tag 030W;
geometric reducedness over a field is a condition on the stalks by Tag 035W. -/
theorem geometricallyReduced_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    GeometricallyReduced ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
      (X ↘ Spec (.of k))) := by
  refine (geometricallyReduced_iff_forall_isGeometricallyReducedAt _).mpr fun w => ?_
  let algSpec : Algebra k ((Spec (.of k)).presheaf.stalk
      (((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).base w)) :=
    StructureSheaf.stalkAlgebra k _
  let algSt : Algebra k ((intersectionWithComplementaryCurve C).presheaf.stalk w) :=
    ((((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
      (X ↘ Spec (.of k))).stalkMap w).hom.comp (algebraMap k _)).toAlgebra
  let algW : Algebra k ((intersectionWithComplementaryCurve C).residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
        (intersectionWithComplementaryCurve C).Γevaluation w).hom.toAlgebra
  have hsep : Algebra.IsSeparableExtension k
      ((intersectionWithComplementaryCurve C).residueField w) :=
    isSeparableExtension_residueField_intersection_bridge hdim hnodal hC w
  have hgr := isGeometricallyReduced_of_isSeparableExtension k
      ((intersectionWithComplementaryCurve C).residueField w) hsep
  have hinj : Function.Injective
      ((intersectionWithComplementaryCurve C).residue w).hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ IsLocalRing.maximalIdeal
        ((intersectionWithComplementaryCurve C).presheaf.stalk w) :=
      (IsLocalRing.residue_eq_zero_iff a).mp ha
    rw [maximalIdeal_stalk_intersection_bridge_eq_bot hdim hnodal hC w] at hmem
    simpa using hmem
  have key : Algebra.IsGeometricallyReduced k
      ((intersectionWithComplementaryCurve C).presheaf.stalk w) := by
    refine Algebra.IsGeometricallyReduced.of_injective
      ({ __ := ((intersectionWithComplementaryCurve C).residue w).hom
         commutes' := fun c => ?_ } :
        (intersectionWithComplementaryCurve C).presheaf.stalk w →ₐ[k]
          (intersectionWithComplementaryCurve C).residueField w) hinj
    rw [Stacks.AlgebraicGeometry.ProperSectionsGeom.algebraMap_stalk_apply k
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))) w c]
    rfl
  exact (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk
    ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))) w).mpr key

/-- **The global functions on the intersection of a rational bridge with the closure of its
complement form a finite etale algebra over the base field.** The intersection is proper over
`k` and geometrically reduced, so clauses (1), (3) and (4) of [Stacks, Tag 0BUG] apply. -/
theorem etale_intersectionSections_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    letI : Algebra k Γ(intersectionWithComplementaryCurve C, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Algebra.Etale k Γ(intersectionWithComplementaryCurve C, ⊤) ∧
      Module.Finite k Γ(intersectionWithComplementaryCurve C, ⊤) := by
  have := geometricallyReduced_intersection_bridge hdim hnodal hC
  exact Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced k
    ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)))

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **The global functions on a rational bridge sit inside those on its intersection with the
closure of its complement as a `k`-subalgebra.** The structure morphism of the intersection over
`k` factors through the bridge, the intersection being a closed subscheme of it. -/
theorem isScalarTower_bridgeSections_intersectionSections
    {C : X.IdealSheafData} (hint : IsIntegral C.subscheme) :
    letI : IsIntegral C.subscheme := hint
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra k Γ(C.subscheme, ⊤) := (bridgeSectionsStructureMap C).hom.toAlgebra
    letI : Algebra k Γ(intersectionWithComplementaryCurve C, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    letI : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
    IsScalarTower k Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) := by
  let : IsIntegral C.subscheme := hint
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra k Γ(C.subscheme, ⊤) := (bridgeSectionsStructureMap C).hom.toAlgebra
  let : Algebra k Γ(intersectionWithComplementaryCurve C, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
        (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
  have hmor := appTop_intersection_subschemeι_comp (k := k) C
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  simp only [RingHom.algebraMap_toAlgebra, bridgeSectionsStructureMap, hmor,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]

/-! ### The assertions of the tag -/

/-- **The field of global functions on a rational bridge is a finite separable extension of the
base field.**  This is the assertion "`k'/k` is a finite separable extension of fields" of
[Stacks, Tag 0E3M], for `C ⊆ X` a rational bridge of a proper one-dimensional at-worst-nodal
curve over `k` with only constant global functions and `k' = Γ(C, 𝒪_C)`.

Finiteness is clause (1) of [Stacks, Tag 0BUG]
(`Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper`): the
bridge is a closed subscheme of `X`, hence proper over `k`.  Separability is the source's appeal
to [Stacks, Tag 0C4D] at a point `w` of `C ∩ X'`, which is nonempty
(`Stacks.Curves.nonempty_intersection_bridge`): that point is a node of `X`, so the residue field
there is separable over `k`
(`Stacks.Curves.isSeparableExtension_residueField_intersection_bridge`), hence geometrically
reduced over `k` by Tag 030W; the evaluation of global functions of the bridge at `w` embeds `k'`
in that residue field, `k'` being a field, so `k'` is geometrically reduced over `k` too and
therefore separable, which for the finite extension `k'/k` is separability in the sense of
`Algebra.IsSeparable`. -/
@[stacks 0E3M "k'/k is a finite separable extension of fields"]
theorem moduleFinite_and_isSeparable_globalSections_bridge
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra k Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Module.Finite k Γ(C.subscheme, ⊤) ∧ Algebra.IsSeparable k Γ(C.subscheme, ⊤) := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let algC : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  have hfin : Module.Finite k Γ(C.subscheme, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
  refine ⟨hfin, ?_⟩
  obtain ⟨w⟩ := nonempty_intersection_bridge hC
  let algW : Algebra k ((intersectionWithComplementaryCurve C).residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
        (intersectionWithComplementaryCurve C).Γevaluation w).hom.toAlgebra
  have hsepW : Algebra.IsSeparableExtension k
      ((intersectionWithComplementaryCurve C).residueField w) :=
    isSeparableExtension_residueField_intersection_bridge hdim hnodal hC w
  have hgrW := isGeometricallyReduced_of_isSeparableExtension k
      ((intersectionWithComplementaryCurve C).residueField w) hsepW
  have hmor := appTop_intersection_subschemeι_comp (k := k) C
  let φ : Γ(C.subscheme, ⊤) →ₐ[k] (intersectionWithComplementaryCurve C).residueField w :=
    { __ := ((Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop ≫
          (intersectionWithComplementaryCurve C).Γevaluation w).hom
      commutes' := fun c => by
        simp only [algC, algW, RingHom.algebraMap_toAlgebra, hmor, CommRingCat.hom_comp,
          RingHom.coe_comp, Function.comp_apply, Category.assoc]
        rfl }
  have hgrC : Algebra.IsGeometricallyReduced k Γ(C.subscheme, ⊤) :=
    Algebra.IsGeometricallyReduced.of_injective φ φ.toRingHom.injective
  have : Algebra.IsSeparableExtension k Γ(C.subscheme, ⊤) :=
    ((Algebra.isSeparableExtension_tfae k Γ(C.subscheme, ⊤) (ringExpChar k)).out 4 1).mp hgrC
  exact Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension k
    Γ(C.subscheme, ⊤)

/-- **The degree two extension `k''/k'` of [Stacks, Tag 0E3M] is either a separable field
extension or the square of `k'`.**  Here `C ⊆ X` is a rational bridge of a proper one-dimensional
at-worst-nodal curve over `k` with only constant global functions, `X'` is the scheme-theoretic
closure of `X \ C`, and `k' = Γ(C, 𝒪_C)`, `k'' = Γ(C ∩ X', 𝒪)`.

The intersection is geometrically reduced over `k`
(`Stacks.Curves.geometricallyReduced_intersection_bridge`), so `k''` is a finite etale
`k`-algebra, and the degree of `k''` over `k'` is two by the defining condition of a rational
bridge; the dichotomy is then
`Stacks.Curves.isField_and_isSeparable_or_algEquiv_prod_of_etale_of_finrank_eq_two`. -/
@[stacks 0E3M "k''/k' is either a degree two separable extension of fields or k'' = k' × k'"]
theorem isField_and_isSeparable_or_algEquiv_prod_intersectionSections_bridge
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
    (IsField Γ(intersectionWithComplementaryCurve C, ⊤) ∧
          Module.finrank Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) = 2 ∧
          Algebra.IsSeparable Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤)) ∨
        Nonempty (Γ(intersectionWithComplementaryCurve C, ⊤) ≃ₐ[Γ(C.subscheme, ⊤)]
          (Γ(C.subscheme, ⊤) × Γ(C.subscheme, ⊤))) := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra k Γ(C.subscheme, ⊤) := (bridgeSectionsStructureMap C).hom.toAlgebra
  let : Algebra k Γ(intersectionWithComplementaryCurve C, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
        (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
  have := isScalarTower_bridgeSections_intersectionSections (k := k) (X := X) hC.isIntegral
  obtain ⟨hetale, hfinite⟩ := etale_intersectionSections_bridge hdim hnodal hC
  have := hetale
  have := hfinite
  have hrank :
      Module.finrank Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) = 2 :=
    hC.intersection_finrank_eq_two
  exact (isField_and_isSeparable_or_algEquiv_prod_of_etale_of_finrank_eq_two k
    Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) hrank).imp_left
    fun h => ⟨h.1, hrank, h.2⟩

end Bridge

end Stacks.Curves

end

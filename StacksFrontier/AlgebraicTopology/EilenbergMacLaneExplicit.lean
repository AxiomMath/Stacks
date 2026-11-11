module

public import StacksFrontier.AlgebraicTopology.EilenbergMacLane
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Abelian

/-!
# The explicit description of `K(A, k)` and the extension of `K(A, k + 1)` by `K(A, k)`

Let `𝒜` be an abelian category, `A` an object of `𝒜` and `k ≥ 0` an integer. The
Eilenberg-MacLane object `K(A, k) = i_{k!}U` of [Stacks, Tag 0191] is
`CategoryTheory.SimplicialObject.eilenbergMacLane A k`, the left Kan extension of the
`k`-truncated simplicial object `U` concentrated in degree `k` with `U_k = A`. Parts (2) and (3)
of [Stacks, Tag 0190] describe it explicitly: its `n`-th term is `⨁_α A` over the surjections
`α : ⦋n⦌ → ⦋k⦌`, and `φ : ⦋m⦌ → ⦋n⦌` sends the summand `α` by the identity to the summand `α ∘ φ`
when that is surjective and to zero otherwise. That explicit simplicial object is
`CategoryTheory.SimplicialObject.EilenbergMacLane.emKAk A k`.

Following the proof of [Stacks, Tag 0190], we show that `emKAk A k` has the universal property of
`i_{k!}U`: a morphism `emKAk A k ⟶ V` is the same as a morphism `f : A ⟶ V_k` killed by every
non-surjective operator into `⦋k⦌`, which by [Stacks, Tag 0190](1) is the same as a morphism
`U ⟶ sk_k V`. This gives an isomorphism `eilenbergMacLane A k ≅ emKAk A k`. Transporting the
short exact sequence `0 → emKAk A k → E → emKAk A (k + 1) → 0` along it gives [Stacks, Tag 0192]
for the Eilenberg-MacLane objects themselves.

## Main definitions

* `CategoryTheory.SimplicialObject.EilenbergMacLane.emKAkDesc`: the morphism `emKAk A k ⟶ V`
  attached to a morphism `A ⟶ V_k` killed by the non-surjective operators into `⦋k⦌`.
* `CategoryTheory.SimplicialObject.EilenbergMacLane.eilenbergMacLaneIsoEmKAk`: the isomorphism
  `K(A, k) = i_{k!}U ≅ emKAk A k`.
* `CategoryTheory.SimplicialObject.EilenbergMacLane.eilenbergMacLaneShortComplex`: the short
  complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` of simplicial objects.

## Main results

* `eilenbergMacLaneShortComplex_shortExact_and_splitting` (in the same namespace): the sequence
  `0 → K(A, k) → E → K(A, k + 1) → 0` is short exact and term by term split.

## References

* [Stacks, Tag 0190](https://stacks.math.columbia.edu/tag/0190)
* [Stacks, Tag 0192](https://stacks.math.columbia.edu/tag/0192)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject.EilenbergMacLane

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasFiniteBiproducts 𝒜] (A : 𝒜)

/-- The summand of `ι_β` under a structure map of `emObject`: the operator attached to `φ` sends
the summand indexed by `β` by the identity to the summand indexed by `φ.unop ≫ β` when that is
admissible, and to zero otherwise. -/
theorem ι_emObject_map (T : SimplexCategory)
    (P : (n : SimplexCategory) → (n ⟶ T) → Prop) [∀ n, DecidablePred (P n)]
    (hP : ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T),
      P c α → P a (g ≫ h ≫ α) → P b (h ≫ α)) {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b)
    (β : {α : a.unop ⟶ T // P a.unop α}) :
    biproduct.ι (fun _ => A) β ≫ (emObject A T P hP).map φ =
      if h : P b.unop (φ.unop ≫ β.1) then biproduct.ι (fun _ => A) ⟨_, h⟩ else 0 := by
  rw [emObject_map]
  refine biproduct.hom_ext _ _ fun γ => ?_
  rw [Category.assoc, biproduct.matrix_π, biproduct.ι_desc]
  by_cases h : P b.unop (φ.unop ≫ β.1)
  · rw [dite_eq_left h]
    by_cases hγ : γ.1 = φ.unop ≫ β.1
    · obtain rfl : γ = ⟨_, h⟩ := Subtype.ext hγ
      rw [ite_eq_left rfl, biproduct.ι_π_self]
    · rw [ite_eq_right hγ, biproduct.ι_π_ne _ (fun e => hγ (congrArg Subtype.val e).symm)]
  · rw [dite_eq_right h, zero_comp, ite_eq_right (fun hγ => h (by rw [← hγ]; exact γ.2))]

/-- The summand of `ι_β` under a structure map of `emKAk A k`: the operator attached to `φ` sends
the summand indexed by a surjection `β` by the identity to the summand indexed by `φ.unop ≫ β`
when that is surjective, and to zero otherwise. -/
theorem ι_emKAk_map {k : ℕ} {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b)
    (β : {α : a.unop ⟶ ⦋k⦌ // coversBelow k α}) :
    biproduct.ι (fun _ => A) β ≫ (emKAk A k).map φ =
      if h : coversBelow k (φ.unop ≫ β.1) then biproduct.ι (fun _ => A) ⟨_, h⟩ else 0 :=
  ι_emObject_map A ⦋k⦌ (fun _ => coversBelow k) (coversBelow_hP k) φ β

/-- A monotone map into `⦋k⦌` covers below `k` if and only if it is surjective. -/
theorem coversBelow_iff_surjective {n : SimplexCategory} {k : ℕ} (α : n ⟶ ⦋k⦌) :
    coversBelow k α ↔ Function.Surjective α.toOrderHom := by
  simp only [coversBelow, imageFinset, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun h i => h i (Nat.le_of_lt_succ i.isLt), fun h i _ => h i⟩

/-- The summand of `(emKAk A k)_k` indexed by the identity of `⦋k⦌`. -/
def topSummand (k : ℕ) : {α : ⦋k⦌ ⟶ ⦋k⦌ // coversBelow k α} :=
  ⟨𝟙 _, (coversBelow_iff_surjective _).mpr fun i => ⟨i, by simp⟩⟩

/-- A morphism out of `emKAk A k` is determined by its restriction to the summand of
`(emKAk A k)_k` indexed by the identity of `⦋k⦌`: the summand indexed by a surjection `α` of
degree `n` is the image of that summand under the operator attached to `α`. -/
theorem emKAk_hom_ext {k : ℕ} {V : SimplicialObject 𝒜} {F G : emKAk A k ⟶ V}
    (h : biproduct.ι (fun _ => A) (topSummand k) ≫ F.app (op ⦋k⦌) =
      biproduct.ι (fun _ => A) (topSummand k) ≫ G.app (op ⦋k⦌)) : F = G := by
  ext n : 2
  obtain ⟨n⟩ := n
  refine biproduct.hom_ext' _ _ fun α => ?_
  have key : biproduct.ι (fun _ => A) (topSummand k) ≫ (emKAk A k).map α.1.op =
      biproduct.ι (fun _ => A) α := by
    rw [ι_emKAk_map, dite_eq_left (by simpa [topSummand] using α.2)]
    congr 1
    exact Subtype.ext (by simp [topSummand])
  rw [← key, Category.assoc, Category.assoc, NatTrans.naturality, NatTrans.naturality,
    reassoc_of% h]

/-- The morphism `emKAk A k ⟶ V` attached to a morphism `f : A ⟶ V_k` killed by every
non-surjective operator into `⦋k⦌`: on the summand indexed by a surjection `α : ⦋n⦌ → ⦋k⦌` it is
`V(α) ∘ f`. This is the construction in the proof of [Stacks, Tag 0190](2)-(3). -/
noncomputable def emKAkDesc {k : ℕ} {V : SimplicialObject 𝒜} (f : A ⟶ V.obj (op ⦋k⦌))
    (hf : ∀ (m : SimplexCategory) (ψ : m ⟶ ⦋k⦌), ¬ coversBelow k ψ → f ≫ V.map ψ.op = 0) :
    emKAk A k ⟶ V where
  app n := biproduct.desc fun α => f ≫ V.map α.1.op
  naturality a b φ := by
    refine biproduct.hom_ext' _ _ fun α => ?_
    rw [← Category.assoc, ι_emKAk_map, biproduct.ι_desc_assoc, Category.assoc,
      ← V.map_comp]
    split_ifs with h
    · rw [biproduct.ι_desc]
      rfl
    · rw [zero_comp]
      exact (hf _ _ h).symm

/-- The morphism `emKAkDesc A f hf` restricts to `f` on the summand indexed by the identity. -/
theorem ι_emKAkDesc_app {k : ℕ} {V : SimplicialObject 𝒜} (f : A ⟶ V.obj (op ⦋k⦌))
    (hf : ∀ (m : SimplexCategory) (ψ : m ⟶ ⦋k⦌), ¬ coversBelow k ψ → f ≫ V.map ψ.op = 0) :
    biproduct.ι (fun _ => A) (topSummand k) ≫ (emKAkDesc A f hf).app (op ⦋k⦌) = f := by
  dsimp only [emKAkDesc]
  rw [biproduct.ι_desc]
  simp [topSummand]

omit [HasFiniteBiproducts 𝒜] in
/-- If `V` vanishes in the degrees below `k`, then every non-surjective operator into `⦋k⦌`
kills every morphism into `V_k`, because it factors through a face map `⦋k - 1⦌ → ⦋k⦌`. -/
theorem comp_map_eq_zero_of_not_coversBelow {k : ℕ} {V : SimplicialObject 𝒜}
    (hV : ∀ j < k, IsZero (V.obj (op ⦋j⦌))) {X : 𝒜} (f : X ⟶ V.obj (op ⦋k⦌))
    {m : SimplexCategory} (ψ : m ⟶ ⦋k⦌) (hψ : ¬ coversBelow k ψ) : f ≫ V.map ψ.op = 0 := by
  rw [coversBelow_iff_surjective] at hψ
  obtain _ | j := k
  · refine absurd (fun i => ⟨0, Fin.ext ?_⟩) hψ
    have h1 := i.isLt
    have h2 := (ψ.toOrderHom 0).isLt
    simp only [SimplexCategory.len_mk] at h1 h2
    omega
  · obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective ψ hψ
    rw [op_comp, V.map_comp,
      (hV j (Nat.lt_succ_self j)).eq_of_tgt (V.map (SimplexCategory.δ i).op) 0, zero_comp,
      comp_zero]

section Iso

variable {k : ℕ} (U : SimplicialObject.Truncated 𝒜 k)
  (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ)) (e : U _⦋k⦌ₖ ≅ A)

omit [HasFiniteBiproducts 𝒜] in
include hU in
/-- The left Kan extension `i_{k!}U` of a `k`-truncated simplicial object vanishing below the top
degree vanishes in the degrees below `k`. -/
theorem isZero_sk_obj (j : ℕ) (hj : j < k) :
    IsZero (((Truncated.sk k).obj U).obj (op ⦋j⦌)) :=
  (hU j hj).of_iso (asIso (((skAdj k).unit.app U).app (op ⦋j, hj.le⦌ₖ))).symm

include hU in
/-- The morphism `e.hom ≫ ι_id : U_k ⟶ (emKAk A k)_k` extends to a morphism of `k`-truncated
simplicial objects `U ⟶ sk_k (emKAk A k)`, by [Stacks, Tag 0190](1). -/
theorem exists_homToEmKAk : ∃ g : U ⟶ (truncation k).obj (emKAk A k),
    g.app (op ⦋k⦌ₖ) = e.hom ≫ biproduct.ι (fun _ => A) (topSummand k) :=
  ((Truncated.app_top_injective_and_exists_iff hU _).1.2 _).mpr fun m φ hφ => by
    change (e.hom ≫ biproduct.ι (fun _ => A) (topSummand k)) ≫ (emKAk A k).map φ.hom.op = 0
    rw [Category.assoc, ι_emKAk_map, dite_eq_right, comp_zero]
    rw [coversBelow_iff_surjective]
    simpa [topSummand] using hφ

include hU in
/-- The morphism `U ⟶ sk_k (emKAk A k)` extending `e.hom ≫ ι_id`. -/
noncomputable def homToEmKAk : U ⟶ (truncation k).obj (emKAk A k) :=
  (exists_homToEmKAk A U hU e).choose

/-- The top component of `homToEmKAk A U hU e` is `e.hom ≫ ι_id`. -/
theorem homToEmKAk_app_top :
    (homToEmKAk A U hU e).app (op ⦋k⦌ₖ) = e.hom ≫ biproduct.ι (fun _ => A) (topSummand k) :=
  (exists_homToEmKAk A U hU e).choose_spec

include hU e in
/-- The morphism `i_{k!}U ⟶ emKAk A k` adjoint to `homToEmKAk`. -/
noncomputable def skObjToEmKAk : (Truncated.sk k).obj U ⟶ emKAk A k :=
  ((skAdj k).homEquiv U _).symm (homToEmKAk A U hU e)

include hU e in
/-- The morphism `emKAk A k ⟶ i_{k!}U` attached to `e.inv` followed by the unit
`U_k ≅ (i_{k!}U)_k`. -/
noncomputable def emKAkToSkObj : emKAk A k ⟶ (Truncated.sk k).obj U :=
  emKAkDesc A (e.inv ≫ ((skAdj k).unit.app U).app (op ⦋k⦌ₖ))
    (fun _ ψ hψ => comp_map_eq_zero_of_not_coversBelow (isZero_sk_obj U hU) _ ψ hψ)

include hU e in
/-- **Stacks 0190** (2)-(3), in general form: for a `k`-truncated simplicial object `U` with
`U_i = 0` for `i < k` and an isomorphism `U_k ≅ A`, the left Kan extension `i_{k!}U` is
isomorphic to the explicit simplicial object `emKAk A k`. -/
noncomputable def skObjIsoEmKAk : (Truncated.sk k).obj U ≅ emKAk A k where
  hom := skObjToEmKAk A U hU e
  inv := emKAkToSkObj A U hU e
  hom_inv_id := by
    refine ((skAdj k).homEquiv U _).injective
      ((Truncated.app_top_injective_and_exists_iff hU _).1.1 ?_)
    dsimp only
    rw [skObjToEmKAk, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Adjunction.homEquiv_id, NatTrans.comp_app, homToEmKAk_app_top]
    change (e.hom ≫ biproduct.ι (fun _ => A) (topSummand k)) ≫
      (emKAkToSkObj A U hU e).app (op ⦋k⦌) = _
    rw [Category.assoc, emKAkToSkObj, ι_emKAkDesc_app]
    exact e.hom_inv_id_assoc _
  inv_hom_id := by
    refine emKAk_hom_ext A ((?_ : _ = biproduct.ι (fun _ => A) (topSummand k)).trans
      (Category.comp_id _).symm)
    rw [NatTrans.comp_app, ← Category.assoc, emKAkToSkObj, ι_emKAkDesc_app]
    have h : (((skAdj k).homEquiv U _) (skObjToEmKAk A U hU e)).app (op ⦋k⦌ₖ) =
        e.hom ≫ biproduct.ι (fun _ => A) (topSummand k) := by
      rw [skObjToEmKAk, Equiv.apply_symm_apply]
      exact homToEmKAk_app_top A U hU e
    exact (Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) h).trans (e.inv_hom_id_assoc _))

end Iso

/-- **Stacks 0190** (2)-(3).
The Eilenberg-MacLane object `K(A, k) = i_{k!}U` of [Stacks, Tag 0191] (the left Kan extension
`eilenbergMacLane A k`) is isomorphic, as a simplicial object, to the explicit simplicial object
`emKAk A k`, whose `n`-th term is `⨁_α A` over the surjections `α : ⦋n⦌ → ⦋k⦌` and whose
operator attached to `φ : ⦋m⦌ → ⦋n⦌` sends the summand `α` by the identity to the summand
`α ∘ φ` when that is surjective and to zero otherwise. -/
@[stacks 0190 "parts (2) and (3): `i_{k!}U` is isomorphic, as a simplicial object, to the \
  simplicial object `emKAk A k` defined by the rules of (2) and (3)"]
noncomputable def eilenbergMacLaneIsoEmKAk (k : ℕ) : eilenbergMacLane A k ≅ emKAk A k :=
  skObjIsoEmKAk A _
    (fun m hm => by
      dsimp only
      rw [ite_eq_right (show ¬ (⦋m⦌ : SimplexCategory).len = k from hm.ne)]
      exact isZero_zero 𝒜)
    (CategoryTheory.eqToIso (by
      dsimp only
      rw [ite_eq_left (rfl : (⦋k⦌ : SimplexCategory).len = k)]))

/-- The short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` of simplicial objects of [Stacks, Tag 0192],
with `K(A, k) = eilenbergMacLane A k` and `K(A, k + 1) = eilenbergMacLane A (k + 1)` the
Eilenberg-MacLane objects of [Stacks, Tag 0191] and `E = emEobj A k`, whose `n`-th term is
`⨁_α A` over the monotone `α : ⦋n⦌ → ⦋k + 1⦌` with image `⦋k⦌` or `⦋k + 1⦌`. Through the
isomorphisms `eilenbergMacLaneIsoEmKAk`, the first map is the inclusion of the summands along the
bottom inclusion `⦋k⦌ ↪ ⦋k + 1⦌` and the second the projection onto the summands indexed by the
surjections. -/
noncomputable def eilenbergMacLaneShortComplex (k : ℕ) : ShortComplex (SimplicialObject 𝒜) :=
  ShortComplex.mk ((eilenbergMacLaneIsoEmKAk A k).hom ≫ emIota A k)
    (emPi A k ≫ (eilenbergMacLaneIsoEmKAk A (k + 1)).inv) (by
      have hz : emIota A k ≫ emPi A k = 0 := (emShortComplex A k).zero
      simp [reassoc_of% hz])

/-- The short complex `emShortComplex A k` of explicit models is isomorphic to
`eilenbergMacLaneShortComplex A k`. -/
noncomputable def emShortComplexIsoEilenbergMacLaneShortComplex (k : ℕ) :
    emShortComplex A k ≅ eilenbergMacLaneShortComplex A k :=
  ShortComplex.isoMk (eilenbergMacLaneIsoEmKAk A k).symm (Iso.refl _)
    (eilenbergMacLaneIsoEmKAk A (k + 1)).symm
    (by simp [eilenbergMacLaneShortComplex, emShortComplex])
    (by simp [eilenbergMacLaneShortComplex, emShortComplex])

/-- **Stacks 0192**.
Let `𝒜` be an abelian category, `A` an object of `𝒜` and `k ≥ 0`. Let `E` be the simplicial
object with `E_n = ⨁_α A` over the monotone `α : ⦋n⦌ → ⦋k + 1⦌` whose image is `⦋k⦌` or
`⦋k + 1⦌`, the operator attached to `φ : ⦋m⦌ → ⦋n⦌` sending the summand `α` by the identity to
the summand `α ∘ φ` when its image is `⦋k⦌` or `⦋k + 1⦌` and to zero otherwise (`emEobj A k`).
Then `0 → K(A, k) → E → K(A, k + 1) → 0`, with `K(A, k)` and `K(A, k + 1)` the Eilenberg-MacLane
objects `i_{k!}U` of [Stacks, Tag 0191], is a short exact sequence of simplicial objects which is
term by term split exact: evaluating it in any degree `n` gives a split short exact sequence
of `𝒜`. -/
@[stacks 0192]
theorem eilenbergMacLaneShortComplex_shortExact_and_splitting (k : ℕ) :
    (eilenbergMacLaneShortComplex A k).ShortExact ∧
      ∀ n : SimplexCategoryᵒᵖ, Nonempty
        (((eilenbergMacLaneShortComplex A k).map ((evaluation _ _).obj n)).Splitting) :=
  ⟨ShortComplex.shortExact_of_iso (emShortComplexIsoEilenbergMacLaneShortComplex A k)
      (emShortComplex_shortExact A k),
    fun n => ⟨(emSplittingApp A k n).ofIso
      ((Functor.mapShortComplex ((evaluation _ _).obj n)).mapIso
        (emShortComplexIsoEilenbergMacLaneShortComplex A k))⟩⟩

end CategoryTheory.SimplicialObject.EilenbergMacLane

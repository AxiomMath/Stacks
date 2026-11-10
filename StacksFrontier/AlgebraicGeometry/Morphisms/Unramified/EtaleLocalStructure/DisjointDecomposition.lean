module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale-local splitting of a separated unramified morphism

Let `f : X ⟶ S` be a separated morphism of schemes which is unramified at finitely many points
`x₁, …, xₙ` lying over a point `s` of `S`. After a single étale base change `U ⟶ S` around `s`
the base change `X ×_S U` decomposes as a disjoint union

  `X ×_S U = W ⊔ ⨆_{i,j} V_{i,j}`

in which every `V_{i,j}` is a closed subscheme of `U` passing through the distinguished point,
and the fibre of `W` over the distinguished point contains no point above any `xᵢ`. If the `xᵢ`
exhaust the fibre of `f` over `s`, that fibre of `W` is empty.

Specialising to a finite unramified morphism, whose fibres are finite, and then removing the
closed image of the remainder `W` from the étale neighbourhood, shows that a finite unramified
morphism becomes a finite disjoint union of closed immersions after an étale base change.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_disjoint_closed_decomposition_of_unramifiedAt` is
  the decomposition described above.
* `AlgebraicGeometry.exists_etaleNeighborhood_disjoint_closed_decomposition_of_finite_unramified`
  is its consequence for a finite unramified morphism.

## Implementation notes

The chosen points are not assumed distinct: the proof passes to the finite set they span before
appealing to `AlgebraicGeometry.exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt`,
which does require distinctness, and then re-indexes the resulting opens by the original index
set, giving the index `i` an empty family of opens whenever `xᵢ` repeats an earlier point.

Separatedness enters only through the closedness of each `V_{i,j}` in the base change: the
composite `V_{i,j} ⟶ U` is a closed immersion and `X ×_S U ⟶ U` is separated, so the open
immersion `V_{i,j} ⟶ X ×_S U` is a closed immersion as well. Deleting from `V_{i,j}` the
(closed) union of the other components therefore leaves an open subscheme which is still closed
over `U`, and these shrunken components are pairwise disjoint.

## References

* [Stacks Project, Tag 04HI](https://stacks.math.columbia.edu/tag/04HI)
* [Stacks Project, Tag 04HJ](https://stacks.math.columbia.edu/tag/04HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Function

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04HI.** A separated morphism of schemes which is unramified at finitely
many points of one fibre becomes, after a single étale base change around the image point, the
disjoint union of finitely many closed subschemes of the new base passing through the
distinguished point and a remainder whose distinguished fibre avoids the chosen points. The
remainder has empty distinguished fibre when the chosen points exhaust the original fibre. -/
@[stacks 04HI]
public theorem exists_etaleNeighborhood_disjoint_closed_decomposition_of_unramifiedAt
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ) (x : Fin n → X) (s : S)
    (hx : ∀ i, f (x i) = s) (hunramified : ∀ i, UnramifiedAt f (x i)) :
    ∃ (U : EtaleNeighborhood S s)
      (W : (pullback f U.toBase).Opens) (m : Fin n → ℕ)
      (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens),
      (sSup (Set.range V) ⊔ W = ⊤) ∧
        (Pairwise (Disjoint on V)) ∧
        (∀ a, Disjoint (V a) W) ∧
        (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f U.toBase)) ∧
        (∀ a, ∃ z : (V a).toScheme,
          ((V a).ι ≫ pullback.snd f U.toBase) z = U.point) ∧
        (∀ (z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point) (i : Fin n),
          ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫
            pullback.fst f U.toBase) z ≠ x i) ∧
    ((∀ y : X, f y = s → ∃ i, y = x i) →
          IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point)) := by
  classical
  -- Enumerate the *distinct* points among the `x i` and apply Tag 04HH to them.
  let P : Set X := Set.range x
  let : Fintype P := (Set.finite_range x).fintype
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  let xp : Fin (Fintype.card P) → X := fun i => (e i).val
  have hxp : Function.Injective xp := fun i j hij => e.injective (Subtype.ext hij)
  have hxp_mem (i) : ∃ j, x j = xp i := (e i).property
  have hpoint : ∀ i, f (xp i) = s := fun i => by
    obtain ⟨j, hj⟩ := hxp_mem i
    rw [← hj]
    exact hx j
  have hunr : ∀ i, UnramifiedAt f (xp i) := fun i => by
    obtain ⟨j, hj⟩ := hxp_mem i
    rw [← hj]
    exact hunramified j
  obtain ⟨U, m₀, V₀, h₀, h₁, h₂⟩ :=
    exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt f _ xp s hpoint hxp hunr
  let Y : Scheme := pullback f U.toBase
  let A := Σ k : Fin (Fintype.card P), Fin (m₀ k)
  let : Fintype A := inferInstance
  -- `r i` is the first index carrying the same point as `i`, and `k i` names that point in the
  -- enumeration of the distinct points. Only the indices `i = r i` receive components.
  let r (i : Fin n) : Fin n :=
    (Finset.univ.filter fun j => x j = x i).min'
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  let k (i : Fin n) : Fin (Fintype.card P) := e.symm ⟨x i, ⟨i, rfl⟩⟩
  let m (i : Fin n) : ℕ := if i = r i then m₀ (k i) else 0
  -- Shrink each component by deleting the (closed) union of the others.
  let E : A → Y.Opens := fun a => ⨆ b : {b : A // b ≠ a}, V₀ b.1
  have hV₀closed (a : A) : IsClosed (V₀ a : Set Y) := by
    let : IsSeparated (pullback.snd f U.toBase) := inferInstance
    let : IsClosedImmersion ((V₀ a).ι ≫ pullback.snd f U.toBase) := (h₀ a).1
    have hV₀ci : IsClosedImmersion (V₀ a).ι :=
      IsClosedImmersion.of_comp (V₀ a).ι (pullback.snd f U.toBase)
    rw [← Scheme.Opens.range_ι]
    exact hV₀ci.isClosedEmbedding.isClosed_range
  have hEclosed (a : A) : IsClosed (E a : Set Y) := by
    change IsClosed ((⨆ b : {b : A // b ≠ a}, V₀ b.1 : Y.Opens) : Set Y)
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isClosed_iUnion_of_finite fun b => hV₀closed b.1
  let V₁ : A → Y.Opens := fun a => ⟨(V₀ a : Set Y) \ (E a : Set Y), (V₀ a).2.sdiff (hEclosed a)⟩
  have hV₁closed (a : A) : IsClosed (V₁ a : Set Y) := (hV₀closed a).sdiff (E a).2
  have hEmem (a : A) (z : Y) : z ∈ E a ↔ ∃ b : A, b ≠ a ∧ z ∈ V₀ b := by
    simp [E]
  have hV₁mem (a : A) (z : Y) : z ∈ V₁ a ↔ z ∈ V₀ a ∧ ∀ b : A, b ≠ a → z ∉ V₀ b := by
    simp [V₁, hEmem]
  have hV₁disj (a b : A) (hab : a ≠ b) : Disjoint (V₁ a) (V₁ b) := by
    refine TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun z hza hzb => ?_)
    exact ((hV₁mem a z).mp hza).2 b hab.symm ((hV₁mem b z).mp hzb).1
  have hrmem (i : Fin n) : r i ∈ Finset.univ.filter (fun j => x j = x i) := Finset.min'_mem _ _
  have hrval (i : Fin n) : x (r i) = x i := (Finset.mem_filter.mp (hrmem i)).2
  have hr_eq (i j : Fin n) (hij : x i = x j) : r i = r j := by simp only [r, hij]
  have hr_idem (i : Fin n) : r (r i) = r i := hr_eq (r i) i (hrval i)
  have hselected (a : Σ i : Fin n, Fin (m i)) : a.1 = r a.1 := by
    by_contra h
    exact Fin.elim0 (Fin.cast (show m a.1 = 0 from ite_eq_right h) a.2)
  let toA (a : Σ i : Fin n, Fin (m i)) : A :=
    ⟨k a.1, Fin.cast (by simp only [m, ite_eq_left (hselected a)]) a.2⟩
  have htoA_inj : Function.Injective toA := by
    intro a b hab
    rcases a with ⟨i, ai⟩
    rcases b with ⟨j, bj⟩
    have hfirst := (Sigma.ext_iff.mp (by simpa [toA] using hab)).1
    have hsub : (⟨x i, ⟨i, rfl⟩⟩ : P) = ⟨x j, ⟨j, rfl⟩⟩ := by
      apply e.symm.injective
      simpa [k] using hfirst
    have hxij : x i = x j := congrArg Subtype.val hsub
    have hij : i = j := by
      calc
        i = r i := hselected ⟨i, ai⟩
        _ = r j := hr_eq i j hxij
        _ = j := (hselected ⟨j, bj⟩).symm
    subst j
    have hsecond := (Sigma.ext_iff.mp (by simpa [toA] using hab)).2
    have hm : m i = m₀ (k i) := by
      dsimp [m]
      rw [ite_eq_left (hselected ⟨i, ai⟩)]
    exact Sigma.ext rfl (heq_of_eq ((Fin.cast_injective hm) (eq_of_heq hsecond)))
  have hV₁le (a : A) : V₁ a ≤ V₀ a := fun z hz => ((hV₁mem a z).mp hz).1
  let g (a : A) := Scheme.Hom.resLE (𝟙 Y) (V₀ a) (V₁ a) (hV₁le a)
  have hg_range (a : A) : Set.range (g a) = Subtype.val ⁻¹' (V₁ a : Set Y) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      change ((g a w).1 : Y) ∈ V₁ a
      have hw : ((g a w).1 : Y) = w.1 := by
        simpa [g, Scheme.Hom.resLE_id] using Scheme.homOfLE_apply (hV₁le a) w
      rw [hw]
      exact w.property
    · intro hz
      refine ⟨⟨z.1, hz⟩, Subtype.ext ?_⟩
      simp [g, Scheme.Hom.resLE_id]
  have hgci (a : A) : IsClosedImmersion (g a) := by
    have : IsOpenImmersion (g a) := by
      simpa [g, Scheme.Hom.resLE_id] using (inferInstance : IsOpenImmersion (Y.homOfLE (hV₁le a)))
    apply IsClosedImmersion.of_isPreimmersion
    rw [hg_range]
    exact (hV₁closed a).preimage continuous_subtype_val
  have hV₁mapci (a : A) : IsClosedImmersion ((V₁ a).ι ≫ pullback.snd f U.toBase) := by
    have hι : g a ≫ (V₀ a).ι = (V₁ a).ι := by
      simpa only [g, Category.comp_id] using
        (Scheme.Hom.resLE_comp_ι (f := 𝟙 Y) (e := hV₁le a))
    rw [← hι, Category.assoc]
    let : IsClosedImmersion (g a) := hgci a
    let : IsClosedImmersion ((V₀ a).ι ≫ pullback.snd f U.toBase) := (h₀ a).1
    infer_instance
  -- Re-index the shrunken components by the original index set, and let `W` be the complement.
  let B := Σ i : Fin n, Fin (m i)
  let : Fintype B := inferInstance
  let V : B → Y.Opens := fun a => V₁ (toA a)
  have hVclosed (a : B) : IsClosed (V a : Set Y) := hV₁closed (toA a)
  let W : Y.Opens :=
    ⟨(⋃ a : B, (V a : Set Y))ᶜ, (isClosed_iUnion_of_finite fun a => hVclosed a).isOpen_compl⟩
  have hdecomp : sSup (Set.range V) ⊔ W = ⊤ := by
    ext y
    by_cases h : ∃ a : B, y ∈ V a
    · simp [W, TopologicalSpace.Opens.coe_sSup, h]
    · have hnot : ∀ a : B, y ∉ V a := fun a ha => h ⟨a, ha⟩
      simp [W, TopologicalSpace.Opens.coe_sSup, hnot]
  have hVpair (a b : B) (hab : a ≠ b) : Disjoint (V a) (V b) := by
    simpa [V] using hV₁disj (toA a) (toA b) fun h => hab (htoA_inj h)
  have hWmem (y : Y) (hyW : y ∈ W) (a : B) : y ∉ V a := fun hyV =>
    (by simpa [W] using hyW : y ∉ (⋃ b : B, (V b : Set Y))) (Set.mem_iUnion.mpr ⟨a, hyV⟩)
  have hVW (a : B) : Disjoint (V a) W :=
    TopologicalSpace.Opens.coe_disjoint.mp
      (Set.disjoint_left.mpr fun y hyV hyW => hWmem y hyW a hyV)
  have hmrep (i : Fin n) : m (r i) = m₀ (k (r i)) := by
    dsimp [m]
    rw [ite_eq_left (hr_idem i).symm]
  -- In the distinguished fibre, no point of a component lies in another, so shrinking loses
  -- nothing there; hence the components still cover the chosen fibre.
  have hexclusive (c : A) (y : Y) (hy : y ∈ V₀ c)
      (hysnd : (pullback.snd f U.toBase) y = U.point) : y ∈ V₁ c :=
    (hV₁mem c y).2 ⟨hy, fun b hbc hyb => (h₁ c b hbc.symm y hy hyb) hysnd⟩
  have hcoverY (y : Y) (hysnd : (pullback.snd f U.toBase) y = U.point)
      (i : Fin n) (hfst : (pullback.fst f U.toBase) y = x i) : ∃ a : B, y ∈ V a := by
    have hfst' : (pullback.fst f U.toBase) y = xp (k (r i)) := by
      calc
        (pullback.fst f U.toBase) y = x i := hfst
        _ = x (r i) := (hrval i).symm
        _ = xp (k (r i)) := by simp [xp, k]
    obtain ⟨j, hj⟩ := h₂ (k (r i)) y hysnd hfst'
    refine ⟨⟨r i, Fin.cast (hmrep i).symm j⟩, ?_⟩
    change y ∈ V₁ (toA ⟨r i, Fin.cast (hmrep i).symm j⟩)
    rw [show toA ⟨r i, Fin.cast (hmrep i).symm j⟩ = ⟨k (r i), j⟩ from
      Sigma.ext rfl (heq_of_eq (by simp [toA, Fin.cast_cast]))]
    exact hexclusive ⟨k (r i), j⟩ y hj hysnd
  have hWavoid (y : Y) (hyw : y ∈ W) (hysnd : (pullback.snd f U.toBase) y = U.point)
      (i : Fin n) (hfst : (pullback.fst f U.toBase) y = x i) : False := by
    obtain ⟨a, ha⟩ := hcoverY y hysnd i hfst
    exact hWmem y hyw a ha
  have hcomponentpoint (a : B) :
      ∃ z : (V a).toScheme, ((V a).ι ≫ pullback.snd f U.toBase) z = U.point := by
    obtain ⟨y, hy, hysnd⟩ := (h₀ (toA a)).2
    have hy₁ := hexclusive (toA a) y hy hysnd
    refine ⟨⟨y, hy₁⟩, ?_⟩
    change (pullback.snd f U.toBase) ((V₁ (toA a)).ι ⟨y, hy₁⟩) = U.point
    simpa only [Scheme.Opens.ι_apply] using hysnd
  let gW := W.ι ≫ pullback.snd f U.toBase
  have hfibsnd (z : gW.fiber U.point) :
      (pullback.snd f U.toBase) (W.ι (gW.fiberι U.point z)) = U.point := by
    change gW (gW.fiberι U.point z) = U.point
    simpa [Scheme.Hom.comp_apply] using congrArg (fun q => q z) (Scheme.Hom.fiber_fac gW U.point)
  have hnoFiber (z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point) (i : Fin n) :
      ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫
        pullback.fst f U.toBase) z ≠ x i := by
    let y : Y := W.ι (gW.fiberι U.point z)
    have hyW : y ∈ W := (gW.fiberι U.point z).property
    have hysnd := hfibsnd z
    intro heq
    exact hWavoid y hyW hysnd i (by simpa [y, gW, Scheme.Hom.comp_apply] using heq)
  refine ⟨U, W, m, V, hdecomp, hVpair, hVW, fun a => by simpa [V] using hV₁mapci (toA a),
    hcomponentpoint, hnoFiber, fun hex => ⟨fun z => ?_⟩⟩
  let y : Y := W.ι (gW.fiberι U.point z)
  have hysnd := hfibsnd z
  have hfs : f ((pullback.fst f U.toBase) y) = s := by
    have hcomm : f ((pullback.fst f U.toBase) y) = U.toBase ((pullback.snd f U.toBase) y) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun q : Y ⟶ S => q y) (pullback.condition (f := f) (g := U.toBase))
    rw [hcomm, hysnd, U.map_point]
  obtain ⟨i, hi⟩ := hex (pullback.fst f U.toBase y) hfs
  exact hnoFiber z i (by simpa [y, gW, Scheme.Hom.comp_apply] using hi)

/-- **Stacks Project, Tag 04HJ.** A finite unramified morphism of schemes becomes a finite
disjoint union of closed immersions after an étale base change around any chosen point of the
target. -/
@[stacks 04HJ]
public theorem exists_etaleNeighborhood_disjoint_closed_decomposition_of_finite_unramified
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f] (s : S) :
    ∃ (U : EtaleNeighborhood S s) (n : ℕ) (V : Fin n → (pullback f U.toBase).Opens),
      (sSup (Set.range V) = ⊤) ∧
        (Pairwise (Disjoint on V)) ∧
        (∀ j, IsClosedImmersion ((V j).ι ≫ pullback.snd f U.toBase)) := by
  classical
  -- The fibre over `s` is finite; apply Tag 04HI to the whole of it.
  let α : Set X := f ⁻¹' {s}
  let : Fintype α := (by simpa [α] using f.finite_preimage_singleton s : α.Finite).fintype
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let x : Fin (Fintype.card α) → X := fun i => e i
  have hx : ∀ i, f (x i) = s := fun i => by
    simpa only [α, Set.mem_preimage, Set.mem_singleton_iff] using (e i).property
  obtain ⟨U, W, m, V, hcover, hdisj, hVW, hclosed, -, hfiber⟩ :=
    exists_etaleNeighborhood_disjoint_closed_decomposition_of_unramifiedAt f _ x s hx
      fun i => Unramified.unramifiedAt (f := f) (x i)
  have hexhaust : ∀ y : X, f y = s → ∃ i, y = x i := fun y hy =>
    ⟨(Fintype.equivFin α) ⟨y, by simpa [α] using hy⟩, by simp [x, e]⟩
  have hWfiber : IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point) := hfiber.2 hexhaust
  let hW := W.ι ≫ pullback.snd f U.toBase
  have hWno : ∀ z : W.toScheme, hW z ≠ U.point := by
    intro z hz
    have hzrange : z ∈ Set.range (hW.fiberι U.point) := by
      rw [hW.range_fiberι U.point]
      simp [hz]
    exact hWfiber.false hzrange.choose
  -- `W` is the complement of the union of the components, hence closed, so its image in the
  -- étale neighbourhood is a closed set missing the distinguished point. Remove it.
  have hWset : W.1 = ((sSup (Set.range V) : (pullback f U.toBase).Opens).1)ᶜ := by
    ext z
    constructor
    · intro hzW hzV
      rw [sSup_range] at hzV
      obtain ⟨a, hza⟩ := TopologicalSpace.Opens.mem_iSup.mp hzV
      have hInf : z ∈ V a ⊓ W := ⟨hza, hzW⟩
      rw [disjoint_iff.mp (hVW a)] at hInf
      simp at hInf
    · intro hznotV
      have htop : z ∈ (sSup (Set.range V) ⊔ W) := by rw [hcover]; simp
      rcases (by simpa only [TopologicalSpace.Opens.coe_sup, Set.mem_union] using htop) with
        hzV | hzW
      · exact (hznotV (by simpa using hzV)).elim
      · exact hzW
  have hWclosed : IsClosed W.1 := by
    rw [hWset]
    exact (sSup (Set.range V)).2.isClosed_compl
  have : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hWclosed)
  let : IsFinite (pullback.snd f U.toBase) := inferInstance
  let : IsFinite hW := inferInstance
  have himageClosed : IsClosed (Set.range hW) := by
    simpa [Set.range] using hW.isClosedMap (Set.univ : Set W.toScheme) isClosed_univ
  let O : U.scheme.Opens := ⟨(Set.range hW)ᶜ, himageClosed.isOpen_compl⟩
  let U' : EtaleNeighborhood S s :=
    { scheme := O.toScheme, point := ⟨U.point, fun ⟨z, hzu⟩ => hWno z hzu⟩,
      toBase := O.ι ≫ U.toBase, map_point := U.map_point }
  let j : O.toScheme ⟶ U.scheme := O.ι
  -- Transport the components along the base change `X ×_S U' = (X ×_S U) ×_U U'`.
  let eP : pullback (pullback.snd f U.toBase) j ≅ pullback f U'.toBase :=
    pullbackLeftPullbackSndIso f U.toBase j
  let k : pullback f U'.toBase ⟶ pullback f U.toBase :=
    eP.inv ≫ pullback.fst (pullback.snd f U.toBase) j
  let Q (a : (Σ i, Fin (m i))) := pullback ((V a).ι ≫ pullback.snd f U.toBase) j
  let eQ (a : (Σ i, Fin (m i))) :=
    pullbackRightPullbackFstIso (pullback.snd f U.toBase) j (V a).ι
  let l (a : (Σ i, Fin (m i))) : Q a ⟶ (V a).toScheme :=
    (eQ a).inv ≫ pullback.fst (V a).ι (pullback.fst (pullback.snd f U.toBase) j)
  let q (a : (Σ i, Fin (m i))) : Q a ⟶ pullback f U'.toBase :=
    (eQ a).inv ≫ pullback.snd (V a).ι (pullback.fst (pullback.snd f U.toBase) j) ≫ eP.hom
  have hq_open (a : (Σ i, Fin (m i))) : IsOpenImmersion (q a) := by
    have : IsOpenImmersion (V a).ι := inferInstance
    have : IsOpenImmersion
        (pullback.snd (V a).ι (pullback.fst (pullback.snd f U.toBase) j)) := inferInstance
    dsimp [q]
    infer_instance
  let C (a : (Σ i, Fin (m i))) : (pullback f U'.toBase).Opens := by
    let := hq_open a
    exact (q a).opensRange
  let morphismMap (a : (Σ i, Fin (m i))) :=
    pullback.map (V a).ι (pullback.fst (pullback.snd f U.toBase) j) (V a).ι k
      (𝟙 _) eP.hom (𝟙 _) (by simp) (by simp [k])
  let E (a : (Σ i, Fin (m i))) : Q a ≅ pullback (V a).ι k :=
    (eQ a).symm ≪≫ asIso (morphismMap a)
  have hE_fst (a : (Σ i, Fin (m i))) : (E a).hom ≫ pullback.fst (V a).ι k = l a := by
    simp [E, l, morphismMap, pullback.map, Category.assoc]
  have hE_snd (a : (Σ i, Fin (m i))) : (E a).hom ≫ pullback.snd (V a).ι k = q a := by
    simp [E, q, morphismMap, pullback.map, Category.assoc]
  have hsq (a : (Σ i, Fin (m i))) : IsPullback (l a) (q a) (V a).ι k := by
    refine IsPullback.of_iso_pullback (i := E a) ⟨?_⟩ (hE_fst a) (hE_snd a)
    calc
      l a ≫ (V a).ι = (E a).hom ≫ pullback.fst (V a).ι k ≫ (V a).ι := by
        simp only [← hE_fst a, Category.assoc]
      _ = (E a).hom ≫ pullback.snd (V a).ι k ≫ k := by
        simpa only [Category.assoc] using
          congrArg ((E a).hom ≫ ·) (pullback.condition (f := (V a).ι) (g := k))
      _ = q a ≫ k := by simp only [← hE_snd a, Category.assoc]
  have hC_eq (a : (Σ i, Fin (m i))) : C a = k ⁻¹ᵁ V a := by
    let : IsOpenImmersion (q a) := hq_open a
    simpa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] using
      IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        (hsq a) (⊤ : (V a).toScheme.Opens)
  have hq_comp (a : (Σ i, Fin (m i))) :
      q a ≫ pullback.snd f U'.toBase =
        pullback.snd ((V a).ι ≫ pullback.snd f U.toBase) j := by
    dsimp [q, eQ]
    rw [Category.assoc, Category.assoc]
    rw [show eP.hom ≫ pullback.snd f U'.toBase = pullback.snd (pullback.snd f U.toBase) j by
      simp [eP, j, U', pullbackLeftPullbackSndIso_hom_snd f U.toBase j]]
    exact pullbackRightPullbackFstIso_inv_snd_snd (pullback.snd f U.toBase) j (V a).ι
  have hCclosed (a : (Σ i, Fin (m i))) :
      IsClosedImmersion ((C a).ι ≫ pullback.snd f U'.toBase) := by
    let : IsClosedImmersion ((V a).ι ≫ pullback.snd f U.toBase) := hclosed a
    have hqclosed : IsClosedImmersion (q a ≫ pullback.snd f U'.toBase) := by
      rw [hq_comp]
      infer_instance
    let : IsOpenImmersion (q a) := hq_open a
    apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (q a).isoOpensRange.hom ((C a).ι ≫ pullback.snd f U'.toBase)).mp
    simpa [C, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc] using hqclosed
  -- Over `U'` the remainder has disappeared, so the transported components cover.
  have hk : k ≫ pullback.snd f U.toBase = pullback.snd f U'.toBase ≫ j := by
    dsimp [k, eP, U', j]
    exact pullbackLeftPullbackSndIso_inv_fst_snd f U.toBase O.ι
  have hpreW : k ⁻¹ᵁ W = ⊥ := by
    refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
    obtain ⟨w, hw⟩ : k z ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    have hzB : (pullback.snd f U.toBase) (k z) ∈ Set.range hW :=
      ⟨w, by simpa [hW] using congrArg (pullback.snd f U.toBase) hw⟩
    have hznotB : j (pullback.snd f U'.toBase z) ∉ Set.range hW :=
      (pullback.snd f U'.toBase z).property
    exact hznotB ((congrArg (fun t : pullback f U'.toBase ⟶ U.scheme => t z) hk) ▸ hzB)
  have hCsup : sSup (Set.range C) = ⊤ := by
    have hkA : k ⁻¹ᵁ (sSup (Set.range V)) = ⊤ := by
      have h := congrArg (fun Z : (pullback f U.toBase).Opens => k ⁻¹ᵁ Z) hcover
      rw [Scheme.Hom.preimage_sup, hpreW] at h
      simpa using h
    rw [sSup_range]
    calc
      (⨆ a, C a) = ⨆ a, k ⁻¹ᵁ V a := by congr 1; funext a; exact hC_eq a
      _ = k ⁻¹ᵁ (⨆ a, V a) := by rw [Scheme.Hom.preimage_iSup]
      _ = k ⁻¹ᵁ (sSup (Set.range V)) := by rw [sSup_range]
      _ = ⊤ := hkA
  have hCpair : Pairwise (Disjoint on C) := by
    intro a b hab
    change Disjoint (C a) (C b)
    rw [hC_eq a, hC_eq b, disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hdisj hab)]
    simp
  -- Finally re-index the components by a `Fin`.
  let β := Σ i, Fin (m i)
  let : Fintype β := inferInstance
  let eb : Fin (Fintype.card β) ≃ β := (Fintype.equivFin β).symm
  have hrangeC : Set.range (fun i : Fin (Fintype.card β) => C (eb i)) = Set.range C := by
    change Set.range (C ∘ eb) = Set.range C
    rw [Set.range_comp]
    simp [eb]
  exact ⟨U', Fintype.card β, fun i => C (eb i), by rw [hrangeC]; exact hCsup,
    fun i j hij => hCpair fun h => hij (eb.injective h), fun i => hCclosed (eb i)⟩

end AlgebraicGeometry

end

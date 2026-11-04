module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeSectionCover
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Sections over a proper modification, and Zariski-local isomorphisms (proof of Stacks 0CQ7)

The middle stages of the proof of [Stacks, Tag 0CQ7] all take place after replacing `Y` by
proper modifications. Here that replacement is never carried out on `𝒳`: the stages are stated
relative to a proper morphism `p : Y' ⟶ Y` from a quasi-compact quasi-separated algebraic space,
with opens `W_k ⊆ Y'` covering `p⁻¹(W)`, sections `x_k : W_k ⟶ 𝒳` of `f` over `p`, and a
quasi-compact open `V' ⊆ p⁻¹(V)`. This is `StageData`.

The main result is the source's passage from stage (e) to stage (f): if `V' ⊆ W_k` for all `k`
and `x_0` and `x_k` are Zariski locally isomorphic over `V'`, then every point of `V'` has a
quasi-compact open neighbourhood over which all of them are isomorphic, finitely many of these
cover `V'` (it is quasi-compact), the section step applies to each, and the finite union of the
resulting section covers covers the image of `V'`.

## Main definitions

* `StageData`: a proper morphism `p : Y' ⟶ Y`, opens `W_k ⊆ Y'` covering `p⁻¹(W)` with sections
  `x_k : W_k ⟶ 𝒳` of `f` over `p`, and a quasi-compact open `V' ⊆ p⁻¹(V) ∩ p⁻¹(W)`.

## Main results

* `le_sheafify_iSup_of_range_subset`: an open subspace whose points are covered by the points of
  finitely many open subspaces lies in the sheafified union of them.
* `StageData.sectionCover_of_locallyIso`: if `V' ⊆ W_k` for all `k` and the sections are Zariski
  locally isomorphic over `V'`, then the image of `V'` has a section cover.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

open ChowGerbeMerge ChowGerbeSectionCover

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Open subspaces covered on points -/

section Opens

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inclusion of subfunctors along `A₀ ≤ A₁ ≤ A₂` is the composite of the two inclusions. -/
lemma homOfLe_trans {A₀ A₁ A₂ : Subfunctor P} (h₀ : A₀ ≤ A₁) (h₁ : A₁ ≤ A₂) :
    Subfunctor.homOfLe (h₀.trans h₁) = Subfunctor.homOfLe h₀ ≫ Subfunctor.homOfLe h₁ :=
  rfl

/-- The points of the source of `a` lie among those of the target of `b` if `a` factors
through `b`. -/
private lemma range_pointsMap_subset_of_comp_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ P} {b : G ⟶ P} (g : F ⟶ G) (h : g ≫ b = a) :
    Set.range (Space.pointsMap B S hS F a) ⊆ Set.range (Space.pointsMap B S hS G b) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨Space.pointsMap B S hS _ g z, by rw [← Space.pointsMap_comp_apply, h]⟩

/-- **An open subspace covered on points by finitely many open subspaces lies in their
sheafified union.** The sheafified union is an open subspace containing every member, so its
points contain those of the given open subspace, which therefore factors through it. -/
theorem le_sheafify_iSup_of_range_subset (hP : IsAlgebraicSpace B S hS P) {n : ℕ}
    (A : Subfunctor P) (C : Fin n → Subfunctor P) (hC : ∀ k, Space.IsOpenSubspace B S hS (C k))
    (h : Set.range (Space.pointsMap B S hS A.toFunctor A.ι) ⊆
      ⋃ k, Set.range (Space.pointsMap B S hS (C k).toFunctor (C k).ι)) :
    A ≤ (⨆ k, C k).sheafify (BigFppfOver.topology B S hS) := by
  have e : (⨆ k, C k) = ⨆ k : ULift.{u} (Fin n), C k.down :=
    le_antisymm (iSup_le fun k => le_iSup_of_le (⟨k⟩ : ULift.{u} (Fin n)) le_rfl)
      (iSup_le fun k => le_iSup_of_le k.down le_rfl)
  rw [e]
  have hι := Space.isOpenImmersion_sheafify_iSup_ι B S hS hP.isSheaf
    (fun k : ULift.{u} (Fin n) => C k.down) (fun k => (hC k.down).2)
  have hU : Space.IsOpenSubspace B S hS
      ((⨆ k : ULift.{u} (Fin n), C k.down).sheafify (BigFppfOver.topology B S hS)) :=
    ⟨AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS _ hι.rep hP, hι⟩
  refine Space.le_of_range_pointsMap_ι_subset B S hS hU (h.trans (Set.iUnion_subset fun k => ?_))
  have hle : C k ≤ (⨆ k : ULift.{u} (Fin n), C k.down).sheafify (BigFppfOver.topology B S hS) :=
    (le_iSup (fun k : ULift.{u} (Fin n) => C k.down) ⟨k⟩).trans (Subfunctor.le_sheafify _ _)
  exact range_pointsMap_subset_of_comp_eq _ (Subfunctor.homOfLe_ι hle)

/-- A point of the image of a morphism is a point of its range subfunctor, and conversely. -/
theorem range_pointsMap_range_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : F ⟶ P) :
    Set.range (Space.pointsMap B S hS (Subfunctor.range m).toFunctor (Subfunctor.range m).ι) =
      Set.range (Space.pointsMap B S hS F m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨z, rfl⟩ := Space.surjective_pointsMap_of_isLocallySurjective B S hS
      (Subfunctor.toRange m) (Presheaf.isLocallySurjective_of_surjective _ _ fun U => by
        rintro ⟨_, y, rfl⟩
        exact ⟨y, rfl⟩) q
    exact ⟨z, by rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  · exact range_pointsMap_subset_of_comp_eq _ (Subfunctor.toRange_ι m)

end Opens

/-! ### The stages, relative to a proper modification -/

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
  (W V : Subfunctor Y)

/-- **The situation of stage (b) of the proof of Stacks 0CQ7, after replacing `Y` by a proper
modification.** A proper morphism `p : Y' ⟶ Y` from a quasi-compact quasi-separated algebraic
space, a quasi-compact open `V' ⊆ p⁻¹(V) ∩ p⁻¹(W)`, quasi-compact opens `W_k ⊆ Y'` of which the
first `n` cover `p⁻¹(W)` on points, and sections `x_k : W_k ⟶ 𝒳` of `f` over `p`. -/
structure StageData (n : ℕ) where
  /-- The modification of `Y`. -/
  Y' : AlgebraicSpaces B S hS
  /-- `Y'` is quasi-compact. -/
  qc : Space.IsQuasiCompactSpace B S hS Y'.1
  /-- `Y'` is quasi-separated. -/
  qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1
  /-- The proper morphism to `Y`. -/
  p : Y'.1 ⟶ Y
  /-- `p` is proper. -/
  hp : Space.IsProper B S hS p
  /-- The open replacing `V`. -/
  V' : Space.OpenSubspaces B S hS Y'.1
  /-- `V'` is quasi-compact. -/
  hV'qc : Space.IsQuasiCompactSpace B S hS V'.1.toFunctor
  /-- `V'` lies in `p⁻¹(V)`. -/
  hV'V : V'.1 ≤ V.preimage p
  /-- `V'` lies in `p⁻¹(W)`. -/
  hV'W : V'.1 ≤ W.preimage p
  /-- The opens carrying sections. -/
  Wi : ℕ → Space.OpenSubspaces B S hS Y'.1
  /-- Each `W_k` is quasi-compact. -/
  hWiqc : ∀ k, Space.IsQuasiCompactSpace B S hS (Wi k).1.toFunctor
  /-- The points of `p⁻¹(W)` are covered by those of `W_0, …, W_{n-1}`. -/
  hcov : Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor (W.preimage p).ι) ⊆
    ⋃ k : Fin n, Set.range (Space.pointsMap B S hS (Wi k).1.toFunctor (Wi k).1.ι)
  /-- The sections. -/
  x : ∀ k, algebraicSpaceStack.{u, w} B S hS (Wi k).1.toFunctor (Wi k).2.1 ⟶ 𝒳
  /-- Each `x_k` is a section of `f` over `p`: `x_k ≫ f` is isomorphic to `W_k ⟶ Y' ⟶ Y`. -/
  hx : ∀ k, Nonempty (x k ≫ f ≅
    algebraicSpaceStackMap.{u, w} B S hS (Wi k).2.1 hY ((Wi k).1.ι ≫ p))

variable {hY f W V}

/-- The points of `Y` reached by `V'`. -/
abbrev StageData.image {n : ℕ} (D : StageData hY f W V n) : Set (Space.points B S hS Y) :=
  Set.range (Space.pointsMap B S hS D.V'.1.toFunctor (D.V'.1.ι ≫ D.p))

/-- With no opens left, `V'` has no points. -/
theorem StageData.sectionCover_zero (hW : Space.IsOpenSubspace B S hS W)
    (D : StageData hY f W V 0) : SectionCover hY f W D.image := by
  refine (SectionCover.iUnion hW (K := PEmpty.{u + 1}) (fun _ => ∅) (fun k => k.elim)).mono ?_
  rintro _ ⟨v, rfl⟩
  exfalso
  have hv : Space.pointsMap B S hS _ D.V'.1.ι v ∈
      Set.range (Space.pointsMap B S hS (W.preimage D.p).toFunctor (W.preimage D.p).ι) :=
    range_pointsMap_subset_of_comp_eq _ (Subfunctor.homOfLe_ι D.hV'W) ⟨v, rfl⟩
  obtain ⟨k, -⟩ := Set.mem_iUnion.1 (D.hcov hv)
  exact k.elim0

/-- The reindexing used to feed the first `m + 1` members to the section step, repeating the
last one. -/
def clampIdx (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => min (k + 1) m

/-- `clampIdx m k` is at most `m`. -/
lemma clampIdx_lt (m k : ℕ) : clampIdx m k < m + 1 := by
  rcases k with _ | k
  · exact Nat.succ_pos m
  · exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- `clampIdx m` is the identity below `m + 1`. -/
lemma clampIdx_of_lt {m k : ℕ} (hk : k < m + 1) : clampIdx m k = k := by
  rcases k with _ | k
  · rfl
  · exact Nat.min_eq_left (by omega)

/-- If `x_0` and `x_k` are Zariski locally isomorphic over `V'` for every `k ≤ m`, then every
point of `V'` has a quasi-compact open neighbourhood in `V'` over which all of them are
isomorphic. -/
private theorem StageData.exists_isQuasiCompact_nbhd_iso {m : ℕ}
    (D : StageData hY f W V (m + 1)) (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1)
    (hloc : ∀ k < m + 1, ∀ v ∈ Set.range (Space.pointsMap B S hS D.V'.1.toFunctor D.V'.1.ι),
      ∃ (O : Subfunctor D.Y'.1) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ D.V'.1),
        v ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi 0).2.1
            (Subfunctor.homOfLe (hOV.trans (hVW 0))) ≫ D.x 0 ≅
          algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi k).2.1
            (Subfunctor.homOfLe (hOV.trans (hVW k))) ≫ D.x k))
    (v : Space.points B S hS D.V'.1.toFunctor) :
    ∃ (N : Subfunctor D.Y'.1) (hN : Space.IsOpenSubspace B S hS N),
      Space.IsQuasiCompactSpace B S hS N.toFunctor ∧
      Space.pointsMap B S hS _ D.V'.1.ι v ∈ Set.range (Space.pointsMap B S hS N.toFunctor N.ι) ∧
      ∃ hNV : N ≤ D.V'.1, ∀ k < m + 1, Nonempty
        (algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi 0).2.1
            (Subfunctor.homOfLe (hNV.trans (hVW 0))) ≫ D.x 0 ≅
          algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi k).2.1
            (Subfunctor.homOfLe (hNV.trans (hVW k))) ≫ D.x k) := by
  choose O hO hOV hvO hiso using fun k : Fin (m + 1) => hloc k k.2 _ ⟨v, rfl⟩
  let U : Set (Space.points B S hS D.Y'.1) :=
    ⋂ k, Set.range (Space.pointsMap B S hS (O k).toFunctor (O k).ι)
  have hUo : _root_.IsOpen U := isOpen_iInter_of_finite fun k =>
    Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (O k).ι (hO k).2
  obtain ⟨N, hN, hNqc, hvN, hNU⟩ :=
    Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS D.Y'.2 U hUo _
      (Set.mem_iInter.2 hvO)
  have hNO : ∀ k, N ≤ O k := fun k =>
    Space.le_of_range_pointsMap_ι_subset B S hS (hO k) (hNU.trans (Set.iInter_subset _ k))
  have hNV : N ≤ D.V'.1 := (hNO 0).trans (hOV 0)
  refine ⟨N, hN, hNqc, hvN, hNV, fun k hk => ?_⟩
  let k' : Fin (m + 1) := ⟨k, hk⟩
  obtain ⟨e⟩ := hiso k'
  let r := algebraicSpaceStackMap.{u, w} B S hS hN.1 (hO k').1 (Subfunctor.homOfLe (hNO k'))
  have e₀ : algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi 0).2.1
        (Subfunctor.homOfLe (hNV.trans (hVW 0))) ≫ D.x 0 =
      r ≫ (algebraicSpaceStackMap.{u, w} B S hS (hO k').1 (D.Wi 0).2.1
        (Subfunctor.homOfLe ((hOV k').trans (hVW 0))) ≫ D.x 0) := by
    rw [← stackMap_comp_assoc, ← homOfLe_trans]
  have e₁ : r ≫ (algebraicSpaceStackMap.{u, w} B S hS (hO k').1 (D.Wi k).2.1
        (Subfunctor.homOfLe ((hOV k').trans (hVW k))) ≫ D.x k) =
      algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi k).2.1
        (Subfunctor.homOfLe (hNV.trans (hVW k))) ≫ D.x k := by
    rw [← stackMap_comp_assoc, ← homOfLe_trans]
  exact ⟨eqToIso e₀ ≪≫ Bicategory.whiskerLeftIso r e ≪≫ eqToIso e₁⟩

/-- The section step over a quasi-compact open `N ⊆ V'` over which all the `x_k` are
isomorphic: the image of `N` has a section cover. -/
private theorem StageData.sectionCover_range_of_forall_iso (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W) {m : ℕ} (D : StageData hY f W V (m + 1))
    (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) {N : Subfunctor D.Y'.1} (hN : Space.IsOpenSubspace B S hS N)
    (hNqc : Space.IsQuasiCompactSpace B S hS N.toFunctor) (hNV : N ≤ D.V'.1)
    (hNiso : ∀ k < m + 1, Nonempty
      (algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi 0).2.1
          (Subfunctor.homOfLe (hNV.trans (hVW 0))) ≫ D.x 0 ≅
        algebraicSpaceStackMap.{u, w} B S hS hN.1 (D.Wi k).2.1
          (Subfunctor.homOfLe (hNV.trans (hVW k))) ≫ D.x k)) :
    SectionCover hY f W (Set.range (Space.pointsMap B S hS N.toFunctor (N.ι ≫ D.p))) := by
  have h := sectionCover_of_mergeData (n := m) (V := Subfunctor.range (N.ι ≫ D.p)) hf hW
    { Y' := D.Y'
      qc := D.qc
      qs := D.qs
      p := D.p
      hp := D.hp
      V' := ⟨N, hN⟩
      hV'qc := hNqc
      hV := (range_pointsMap_range_ι _).le
      hV'W := hNV.trans D.hV'W
      Wi := fun j => D.Wi (clampIdx m j)
      hWiqc := fun j => D.hWiqc _
      hcov := le_sheafify_iSup_of_range_subset D.Y'.2 _ _ (fun j => (D.Wi _).2) (fun y hy => by
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (D.hcov hy)
        exact Set.mem_iUnion.2 ⟨j, by rwa [clampIdx_of_lt j.2]⟩)
      hVW := fun j => hNV.trans (hVW _)
      x := fun j => D.x (clampIdx m j)
      hx := fun j => D.hx _
      φ := fun j => hNiso _ (clampIdx_lt m j) }
  rwa [range_pointsMap_range_ι] at h

/-- **Stage (e) to stage (f) of the proof of Stacks 0CQ7.** If `V' ⊆ W_k` for every `k` and, for
every `k < n`, the sections `x_0` and `x_k` are Zariski locally isomorphic over `V'`, then the
image of `V'` has a section cover: around every point of `V'` there is a quasi-compact open over
which all of them are isomorphic; finitely many of these cover `V'`; the section step applies to
each, and the finite union of the results covers the image of `V'`. -/
theorem StageData.sectionCover_of_locallyIso (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W) {n : ℕ} (D : StageData hY f W V n)
    (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1)
    (hloc : ∀ k < n, ∀ v ∈ Set.range (Space.pointsMap B S hS D.V'.1.toFunctor D.V'.1.ι),
      ∃ (O : Subfunctor D.Y'.1) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ D.V'.1),
        v ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi 0).2.1
            (Subfunctor.homOfLe (hOV.trans (hVW 0))) ≫ D.x 0 ≅
          algebraicSpaceStackMap.{u, w} B S hS hO.1 (D.Wi k).2.1
            (Subfunctor.homOfLe (hOV.trans (hVW k))) ≫ D.x k)) :
    SectionCover hY f W D.image := by
  classical
  rcases n with _ | m
  · exact D.sectionCover_zero hW
  -- a quasi-compact open neighbourhood of every point over which all the `x_k` agree
  choose N hN hNqc hvN hNV hNiso using D.exists_isQuasiCompact_nbhd_iso hVW hloc
  have hcpt : CompactSpace (Space.points B S hS D.V'.1.toFunctor) :=
    (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _ D.V'.2.1).1 D.hV'qc
  -- finitely many of them cover `V'`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun v => Space.pointsMap B S hS _ D.V'.1.ι ⁻¹'
      Set.range (Space.pointsMap B S hS (N v).toFunctor (N v).ι))
    (fun v => (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (N v).ι (hN v).2).preimage
      (Space.continuous_pointsMap B S hS _))
    (fun v _ => Set.mem_iUnion.2 ⟨v, hvN v⟩)
  let vs : ULift.{u} (Fin t.card) → Space.points B S hS D.V'.1.toFunctor :=
    fun k => (t.equivFin.symm k.down).1
  -- the section step on each of them
  refine (SectionCover.iUnion hW _ fun k => D.sectionCover_range_of_forall_iso hf hW hVW
    (hN (vs k)) (hNqc _) (hNV _) (hNiso _)).mono ?_
  rintro _ ⟨v, rfl⟩
  obtain ⟨i, hi, z, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
  refine Set.mem_iUnion.2 ⟨⟨t.equivFin ⟨i, hi⟩⟩, ?_⟩
  rw [show vs ⟨t.equivFin ⟨i, hi⟩⟩ = i by simp only [vs, Equiv.symm_apply_apply]]
  exact ⟨z, by rw [Space.pointsMap_comp_apply, Space.pointsMap_comp_apply, hz]⟩

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

end

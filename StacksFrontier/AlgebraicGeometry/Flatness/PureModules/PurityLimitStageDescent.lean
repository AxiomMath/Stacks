module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageDirected
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible

/-!
# Descending a neighbourhood inside a locally constructible set to a finite stage

Let `S = lim S_k` be the limit of a directed inverse system of affine schemes, let `B` be an
affine scheme over the stage `S_i`, and let `E ⊆ B` be locally constructible. Write
`B_k = B ×_{S_i} S_k` for `k ≥ i` and `B_∞ = B ×_{S_i} S`, and write `pr` for the projections to
`B`. If the inverse image `pr⁻¹(E) ⊆ B_∞` contains a neighbourhood of a point `z`, then already
at some finite stage `k` the inverse image `pr⁻¹(E) ⊆ B_k` contains a neighbourhood of the image
of `z`.

This is the limit-theoretic half of the proof that purity passes to a finite stage in Tag 05MA.
It combines Tag 01Z4 — a quasi-compact open of the limit comes from a stage — with Tag 05F4 —
a locally constructible subset of a stage containing the image of the limit already contains the
image of a later stage.

## Main results

* `AlgebraicGeometry.exists_stage_isOpen_subset_preimage_of_mem_nhds_preimage` is the statement
  above.

## Implementation notes

Tag 05F4 is applied to the set `pr⁻¹(E) ∪ Vᶜ`, where `V` is the quasi-compact open of the stage
which Tag 01Z4 produces from an affine open neighbourhood of `z` inside `pr⁻¹(E)`: its inverse
image at a later stage is contained in `pr⁻¹(E)` exactly on `V`, which is what is wanted, and
the complement of a quasi-compact open of an affine scheme is constructible. The alternative —
applying Tag 05F4 to the inverse system of the opens themselves — needs the base change of the
system a second time and gains nothing.

Every stage of the base-changed system is affine, so the compactness and quasi-separatedness
required of a `AlgebraicGeometry.DescentSituation` hold, and so does the prespectrality needed
for the complement of a quasi-compact open to be constructible.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 05MA](https://stacks.math.columbia.edu/tag/05MA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter Opposite Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Descending a neighbourhood inside a locally constructible set.** Let `S` be the limit of a
directed inverse system of affine schemes `S_k`, let `B` be an affine scheme over the stage
`S_i` and let `E ⊆ B` be locally constructible. If the inverse image of `E` in `B ×_{S_i} S`
contains a neighbourhood of a point `z`, then for some `k ≥ i` the inverse image of `E` in
`B ×_{S_i} S_k` contains a neighbourhood of the image of `z`. -/
public theorem exists_stage_isOpen_subset_preimage_of_mem_nhds_preimage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ k : Iᵒᵖ, IsAffine (D.obj k)]
    (c : Cone D) (hc : IsLimit c) (i : I) {B : Scheme.{u}} [IsAffine B]
    (w : B ⟶ D.obj (op i)) {E : Set B} (hE : IsLocallyConstructible E)
    (z : (pullback (c.π.app (op i)) w : Scheme.{u}))
    (hz : pullback.snd (c.π.app (op i)) w ⁻¹' E ∈ 𝓝 z) :
    ∃ (k : I) (hik : i ≤ k)
      (t : (pullback (c.π.app (op i)) w : Scheme.{u}) ⟶ pullback (D.map (homOfLE hik).op) w)
      (V : Set (pullback (D.map (homOfLE hik).op) w : Scheme.{u})),
      t ≫ pullback.fst (D.map (homOfLE hik).op) w =
          pullback.fst (c.π.app (op i)) w ≫ c.π.app (op k) ∧
        t ≫ pullback.snd (D.map (homOfLE hik).op) w = pullback.snd (c.π.app (op i)) w ∧
        IsOpen V ∧ t z ∈ V ∧ V ⊆ pullback.snd (D.map (homOfLE hik).op) w ⁻¹' E := by
  classical
  have haff : ∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e) := fun e =>
    isAffineHom_of_isAffine _
  set Dsys := directedBaseChangeDiagram D i w with hDsys
  set cb := directedBaseChangeCone D i w c with hcbdef
  have hcb : IsLimit cb := isLimitDirectedBaseChangeCone D i w c hc
  have hstageAff : ∀ k : {k : I // i ≤ k},
      IsAffine (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}) := by
    intro k
    have h1 : IsAffineHom (D.map (homOfLE k.2).op) := haff _
    have h2 : IsAffineHom (pullback.snd (D.map (homOfLE k.2).op) w) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (D.map (homOfLE k.2).op) w) h1
    exact isAffine_of_isAffineHom (pullback.snd (D.map (homOfLE k.2).op) w)
  have hDsysAff : ∀ {a b : {k : I // i ≤ k}ᵒᵖ} (e : a ⟶ b), IsAffineHom (Dsys.map e) :=
    fun e => isAffineHom_directedBaseChangeDiagram_map D i w e
  have hap : ∀ {X Y : Scheme.{u}} {f g : X ⟶ Y}, f = g → ∀ x, f x = g x := fun h x => h ▸ rfl
  -- An affine open neighbourhood of `z` inside the inverse image of `E`.
  obtain ⟨V₀, hV₀le, hV₀open, hV₀mem⟩ := mem_nhds_iff.mp hz
  obtain ⟨Vaff, hVaff, hzVaff, hVaffle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := cb.pt) (x := z)
      (U := ⟨V₀, hV₀open⟩) hV₀mem
  -- Tag 01Z4: the affine open comes from a finite stage.
  obtain ⟨jj, Vj, hVjcpt, hVjpre⟩ :=
    have : ∀ {a b : {k : I // i ≤ k}ᵒᵖ} (e : a ⟶ b), IsAffineHom (Dsys.map e) := hDsysAff
    exists_preimage_eq Dsys cb hcb Vaff hVaff.isCompact
  obtain ⟨j, hj⟩ : ∃ j : {k : I // i ≤ k}, jj = op j := ⟨jj.unop, rfl⟩
  subst hj
  -- Tag 05F4 applied to the inverse image of `E` together with the complement of `Vj`.
  have hjAff : IsAffine (Dsys.obj (op j)) := hstageAff j
  have hEjlc : Topology.IsLocallyConstructible
      (pullback.snd (D.map (homOfLE j.2).op) w ⁻¹' E ∪ (Vj : Set (Dsys.obj (op j)))ᶜ) := by
    refine (isLocallyConstructible_preimage
      (pullback.snd (D.map (homOfLE j.2).op) w) hE).union ?_
    exact ((hVjcpt.isConstructible Vj.2).compl).isLocallyConstructible
  have hlim : Set.range ⇑(cb.π.app (op j)) ⊆
      pullback.snd (D.map (homOfLE j.2).op) w ⁻¹' E ∪ (Vj : Set (Dsys.obj (op j)))ᶜ := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : (cb.π.app (op j)) x ∈ (Vj : Set (Dsys.obj (op j)))
    · refine Or.inl ?_
      have hxV : x ∈ cb.π.app (op j) ⁻¹ᵁ Vj := hx
      rw [hVjpre] at hxV
      have hxE : x ∈ pullback.snd (c.π.app (op i)) w ⁻¹' E := hV₀le (hVaffle hxV)
      have hcompat : pullback.snd (D.map (homOfLE j.2).op) w ((cb.π.app (op j)) x) =
          pullback.snd (c.π.app (op i)) w x :=
        hap (directedBaseChangeCone_π_snd D i w c j) x
      show pullback.snd (D.map (homOfLE j.2).op) w ((cb.π.app (op j)) x) ∈ E
      rw [hcompat]
      exact hxE
    · exact Or.inr hx
  obtain ⟨k, hjk, hrange⟩ := exists_stage_range_subset_of_isLocallyConstructible D i w c hc
    (fun k => have := hstageAff k; inferInstance)
    (fun k => have := hstageAff k; inferInstance) j _ hEjlc hlim
  refine ⟨k.1, k.2, cb.π.app (op k),
    (Dsys.map (homOfLE hjk).op) ⁻¹' (Vj : Set (Dsys.obj (op j))), ?_, ?_, ?_, ?_, ?_⟩
  · exact directedBaseChangeCone_π_fst D i w c k
  · exact directedBaseChangeCone_π_snd D i w c k
  · exact Vj.2.preimage (Dsys.map (homOfLE hjk).op).continuous
  · have hwz : (Dsys.map (homOfLE hjk).op) ((cb.π.app (op k)) z) = (cb.π.app (op j)) z :=
      hap (cb.w (homOfLE hjk).op) z
    show (Dsys.map (homOfLE hjk).op) ((cb.π.app (op k)) z) ∈ (Vj : Set (Dsys.obj (op j)))
    rw [hwz]
    have hzV : z ∈ cb.π.app (op j) ⁻¹ᵁ Vj := by rw [hVjpre]; exact hzVaff
    exact hzV
  · intro y hy
    have hyrange := hrange (Set.mem_range_self (f := ⇑(Dsys.map (homOfLE hjk).op)) y)
    have hyV : (Dsys.map (homOfLE hjk).op) y ∈ (Vj : Set (Dsys.obj (op j))) := hy
    have hyE : (Dsys.map (homOfLE hjk).op) y ∈
        pullback.snd (D.map (homOfLE j.2).op) w ⁻¹' E := by
      rcases hyrange with h | h
      · exact h
      · exact absurd hyV h
    have hcy : pullback.snd (D.map (homOfLE j.2).op) w
        ((Dsys.map (homOfLE hjk).op) y) = pullback.snd (D.map (homOfLE k.2).op) w y :=
      hap (directedBaseChangeDiagram_map_snd D i w (homOfLE hjk).op) y
    show pullback.snd (D.map (homOfLE k.2).op) w y ∈ E
    rw [← hcy]
    exact hyE

end AlgebraicGeometry

end

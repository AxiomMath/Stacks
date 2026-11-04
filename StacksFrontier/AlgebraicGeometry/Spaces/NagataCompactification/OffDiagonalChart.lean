module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalSeparation

/-!
# The chart of the repaired gluing step of Stacks 0F4B

Let `π : X ⟶ Y` be proper over a Noetherian algebraic space `Y`, `ι : V ⟶ X` an open immersion
and `ψ : V ⟶ U` proper with `ψ ≫ q = ι ≫ π`. Let `j : U₁ ⟶ V` be an open immersion such that
`f = j ≫ ψ` is étale and an isomorphism over the reduced closed subspace on a closed set
`Z ⊆ |U|`. After three `V`-admissible blowups `X' ⟶ X`, the steps R0, R1 and R2 of the repair
(`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_closure_image`,
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_offDiagonal_separated` and
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_closure_boundary`), there is an open
set `N` of points of `X'` such that

* (N1) `N` contains `U₁` and (N2) meets `V` exactly in `U₁`;
* (N3) `N` contains the closure of `f⁻¹ Z`;
* (N4) for every closed set `K` of points of `U₁ ×_U U₁` off the diagonal, the image of `K` in
  `X' ×_Y X'` is closed among the points with both coordinates in `N`.

The set `N` is the complement of the closures of `V ∖ U₁` and of the part of the boundary of `X'`
lying over the boundary of the second blowup outside the closed set `R` of step R1. In (N4) a
point of the closure with a coordinate in `V` comes from `V ×_U V` (Lemma 1 of the repair), hence
from `U₁ ×_U U₁` by (N2); a point with both coordinates on the boundary has both coordinates over
`R`, which step R1 excludes.

## Main results

* `AlgebraicGeometry.Space.exists_isProper_offDiagonal_chart`: the blowup `X'` and the open `N`
  with (N1)-(N4).

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 0F46](https://stacks.math.columbia.edu/tag/0F46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

/-! ### The point-set part -/

section PointSet

variable {α X₀ X₁ X₂ : Type*} [TopologicalSpace α] [TopologicalSpace X₀] [TopologicalSpace X₁]
  [TopologicalSpace X₂] {ι₀ : α → X₀} {ι₁ : α → X₁} {ι₂ : α → X₂} {c : X₂ → X₀} {b : X₂ → X₁}
  {A₁ A₂ : Set α} {R C : Set X₁}

omit [TopologicalSpace X₁] in
/-- **(N1) and (N2), point-set form.** For an open embedding `ι₂` with `b⁻¹ (range ι₁) = range ι₂`
and `A₂` closed, the complement `N` of `closure (ι₂ '' A₂) ∪ closure (b⁻¹ ((range ι₁)ᶜ \ R))` meets
`range ι₂` exactly in `ι₂ '' A₂ᶜ`. -/
theorem inter_range_compl_closure_union_closure_eq (hι₂ : IsOpenEmbedding ι₂)
    (hb : b ⁻¹' Set.range ι₁ = Set.range ι₂) (hA₂ : IsClosed A₂) :
    (closure (ι₂ '' A₂) ∪ closure (b ⁻¹' ((Set.range ι₁)ᶜ \ R)))ᶜ ∩ Set.range ι₂ =
      ι₂ '' A₂ᶜ := by
  have hcl : closure (b ⁻¹' ((Set.range ι₁)ᶜ \ R)) ⊆ (Set.range ι₂)ᶜ := by
    refine closure_minimal (fun x hx => ?_) hι₂.isOpen_range.isClosed_compl
    rw [← hb]
    exact hx.1
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨hN, a, rfl⟩
    exact ⟨a, fun ha => hN (Or.inl (subset_closure ⟨a, ha, rfl⟩)), rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, a, rfl⟩
    rintro (h | h)
    · obtain ⟨a', ha', he⟩ := (hι₂.closure_image_inter_range hA₂).subset ⟨h, a, rfl⟩
      exact ha (hι₂.injective he ▸ ha')
    · exact hcl h ⟨a, rfl⟩

omit [TopologicalSpace α] [TopologicalSpace X₁] in
/-- **(N3), point-set form.** The closure of `ι₂ '' A₁` lies in the chart `N` when the closures
of `ι₀ '' A₁` and `ι₀ '' A₂` are disjoint (step R0, transported along `c` with `c ∘ ι₂ = ι₀`) and
the closures of `b⁻¹ (C ∩ range ι₁)` and `b⁻¹ ((range ι₁)ᶜ \ R)` are disjoint, with
`ι₁ '' A₁ ⊆ C` (step R2). -/
theorem closure_image_subset_compl_closure_union_closure (hc : Continuous c)
    (hcι : ∀ a, c (ι₂ a) = ι₀ a) (hbι : ∀ a, b (ι₂ a) = ι₁ a)
    (h₀ : Disjoint (closure (ι₀ '' A₁)) (closure (ι₀ '' A₂))) (hA₁C : ι₁ '' A₁ ⊆ C)
    (h₂ : Disjoint (closure (b ⁻¹' (C ∩ Set.range ι₁))) (closure (b ⁻¹' ((Set.range ι₁)ᶜ \ R)))) :
    closure (ι₂ '' A₁) ⊆ (closure (ι₂ '' A₂) ∪ closure (b ⁻¹' ((Set.range ι₁)ᶜ \ R)))ᶜ := by
  have himage : ∀ A : Set α, c '' (ι₂ '' A) = ι₀ '' A := fun A => by
    rw [Set.image_image]; simp_rw [hcι]
  intro y hy hy'
  rcases hy' with hy' | hy'
  · have h₁ : c y ∈ closure (ι₀ '' A₁) := by
      rw [← himage A₁]; exact image_closure_subset_closure_image hc ⟨y, hy, rfl⟩
    have h₂' : c y ∈ closure (ι₀ '' A₂) := by
      rw [← himage A₂]; exact image_closure_subset_closure_image hc ⟨y, hy', rfl⟩
    exact Set.disjoint_left.1 h₀ h₁ h₂'
  · refine Set.disjoint_left.1 h₂ (closure_mono ?_ hy) hy'
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨hbι a ▸ hA₁C ⟨a, ha, rfl⟩, a, (hbι a).symm⟩

omit [TopologicalSpace α] [TopologicalSpace X₁] in
/-- **The boundary points of the chart lie over `R`.** A point of `N` outside `range ι₂` maps by
`b` into `R`, when `b⁻¹ (range ι₁) = range ι₂`. -/
theorem mem_of_mem_compl_closure_union_closure (hb : b ⁻¹' Set.range ι₁ = Set.range ι₂)
    {x : X₂} (hx : x ∈ (closure (ι₂ '' A₂) ∪ closure (b ⁻¹' ((Set.range ι₁)ᶜ \ R)))ᶜ)
    (hx₂ : x ∉ Set.range ι₂) : b x ∈ R := by
  by_contra hR
  refine hx (Or.inr (subset_closure ⟨fun h => hx₂ ?_, hR⟩))
  rw [← hb]
  exact h

end PointSet

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- Fibre products of presheaves on the site, resolved in one instance step: the general search
for `HasPullback f g` among presheaves wanders through adhesive and enriched categories, and
the statements below form several such fibre products. -/
private instance (priority := high) presheafHasPullback
    {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X₀ ⟶ Z₀) (g : Y₀ ⟶ Z₀) :
    HasPullback f g := inferInstance

/-- **(N4) at a point with both coordinates on the boundary.** Let `b : X₂ ⟶ X₁` be a morphism over
`Y` and `e₂ : U₁ ⟶ X₂` a lift of `e₁ : U₁ ⟶ X₁`. Suppose no point of the closure of the
off-diagonal points of `X₁ ×_Y X₁` has both coordinates in `R`. Then no point of the closure of
the off-diagonal points of `X₂ ×_Y X₂` has both coordinates over `R`: its image under `b × b` would
be such a point. -/
theorem false_of_mem_closure_offDiagonal_of_comp {Y X₁ X₂ U₁ U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : U₁ ⟶ U} {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} {b : X₂ ⟶ X₁} (hb : b ≫ π₁ = π₂)
    {e₁ : U₁ ⟶ X₁} {e₂ : U₁ ⟶ X₂} (he : e₂ ≫ b = e₁) {R : Set (points B S hS X₁)}
    (hR : ∀ ρ₁ : pullback f f ⟶ pullback π₁ π₁,
      ρ₁ ≫ pullback.fst π₁ π₁ = pullback.fst f f ≫ e₁ →
      ρ₁ ≫ pullback.snd π₁ π₁ = pullback.snd f f ≫ e₁ →
      ∀ w ∈ closure (pointsMap B S hS _ ρ₁ ''
          (Set.range (pointsMap B S hS U₁ (pullback.diagonal f)))ᶜ),
        pointsMap B S hS (pullback π₁ π₁) (pullback.fst π₁ π₁) w ∈ R →
        pointsMap B S hS (pullback π₁ π₁) (pullback.snd π₁ π₁) w ∈ R → False)
    {ρ₂ : pullback f f ⟶ pullback π₂ π₂}
    (h₁ : ρ₂ ≫ pullback.fst π₂ π₂ = pullback.fst f f ≫ e₂)
    (h₂ : ρ₂ ≫ pullback.snd π₂ π₂ = pullback.snd f f ≫ e₂)
    {w : points B S hS (pullback π₂ π₂)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ₂ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal f)))ᶜ))
    (hw₁ : pointsMap B S hS _ b (pointsMap B S hS _ (pullback.fst π₂ π₂) w) ∈ R)
    (hw₂ : pointsMap B S hS _ b (pointsMap B S hS _ (pullback.snd π₂ π₂) w) ∈ R) : False := by
  subst hb he
  let ρ₀ := pullback.map (b ≫ π₁) (b ≫ π₁) π₁ π₁ b b (𝟙 Y) (by simp) (by simp)
  have hmaps : Set.MapsTo (pointsMap B S hS _ ρ₀)
      (pointsMap B S hS _ ρ₂ '' (Set.range (pointsMap B S hS U₁ (pullback.diagonal f)))ᶜ)
      (pointsMap B S hS _ (ρ₂ ≫ ρ₀) ''
        (Set.range (pointsMap B S hS U₁ (pullback.diagonal f)))ᶜ) := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [pointsMap_comp_apply]⟩
  refine hR (ρ₂ ≫ ρ₀) (by simp [ρ₀, reassoc_of% h₁]) (by simp [ρ₀, reassoc_of% h₂])
    (pointsMap B S hS _ ρ₀ w) (map_mem_closure (continuous_pointsMap B S hS _) hw hmaps) ?_ ?_
  · rwa [← pointsMap_comp_apply, show ρ₀ ≫ pullback.fst π₁ π₁ = pullback.fst _ _ ≫ b by simp [ρ₀],
      pointsMap_comp_apply]
  · rwa [← pointsMap_comp_apply, show ρ₀ ≫ pullback.snd π₁ π₁ = pullback.snd _ _ ≫ b by simp [ρ₀],
      pointsMap_comp_apply]


section Chart

variable {X Y : AlgebraicSpaces B S hS} {π : X ⟶ Y} {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ι : V ⟶ X.1} {ψ : V ⟶ U} {q : U ⟶ Y.1} {j : U₁ ⟶ V}
  {ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom}
  (hρ₁ : ρ ≫ pullback.fst π.hom π.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
  (hρ₂ : ρ ≫ pullback.snd π.hom π.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
  (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
  (hψ : IsProper B S hS ψ) (hπ : IsSeparated B S hS π.hom) (hι : IsOpenImmersion B S hS ι)
  (h : ψ ≫ q = ι ≫ π.hom)

include hρ₁ hρ₂ hV hU hψ hπ hι h in
/-- **Lemma 1 for either coordinate.** A point of the closure of the off-diagonal points with a
coordinate in `V` comes from `V ×_U V`. -/
theorem mem_range_of_mem_closure_offDiagonal_of_mem_range
    {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (hwV : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι) ∨
      pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι)) :
    w ∈ Set.range (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp))) :=
  hwV.elim (mem_range_of_mem_closure_offDiagonal_of_fst_mem hρ₁ hρ₂ hV hU hψ hπ hι h hw)
    (mem_range_of_mem_closure_offDiagonal_of_snd_mem hρ₁ hρ₂ hV hU hψ hπ hι h hw)

include hρ₁ hρ₂ hV hU hψ hπ hι h in
/-- **(N4) at a point with a coordinate in `V`.** Let `N` be a set of points of `X` meeting `V`
only in `U₁`, and `K` a closed set of points of `U₁ ×_U U₁` off the diagonal. A point of the
closure of the image of `K` in `X ×_Y X` with both coordinates in `N` and one of them in `V` lies
in the image of `K`: by Lemma 1 it comes from `V ×_U V`, then from `U₁ ×_U U₁`, on which the map to
`X ×_Y X` is an embedding. -/
theorem mem_image_of_mem_closure_image_of_mem_range (hj : IsOpenImmersion B S hS j)
    {N : Set (points B S hS X.1)}
    (hN : N ∩ Set.range (pointsMap B S hS V ι) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι)))
    {K : Set (points B S hS (pullback (j ≫ ψ) (j ≫ ψ)))} (hK : IsClosed K)
    (hKΔ : Disjoint K (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ)))))
    {w : points B S hS (pullback π.hom π.hom)} (hw : w ∈ closure (pointsMap B S hS _ ρ '' K))
    (hw₁ : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ N)
    (hw₂ : pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ N)
    (hwV : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι) ∨
      pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι)) :
    w ∈ pointsMap B S hS _ ρ '' K := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have hιinj := pointsMap_injective_of_mono B S hS ι
  let a := pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h
  let j₁ := pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp)
  let m := pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp)
  have hρ : ρ = m ≫ a ≫ j₁ := eq_pullbackMap_comp_of_fst_snd hρ₁ hρ₂ h
  have : Mono m := mono_pullbackMap (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) _ _
  have hemb := isEmbedding_pointsMap_pullbackMap_comp B S hS hV hU X.2 Y.2 hψ hπ hι h
  have hmemb : IsOpenEmbedding (pointsMap B S hS _ m) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _)
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _
        (isOpenImmersion_pullbackMap_of_isOpenImmersion j ψ hj))
  have hwO : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) :=
    closure_mono (Set.image_mono fun k hk hkΔ => Set.disjoint_left.1 hKΔ hk hkΔ) hw
  obtain ⟨v, rfl⟩ :=
    mem_range_of_mem_closure_offDiagonal_of_mem_range hρ₁ hρ₂ hV hU hψ hπ hι h hwO hwV
  have he₁ : (a ≫ j₁) ≫ pullback.fst π.hom π.hom = pullback.fst ψ ψ ≫ ι := by simp [a, j₁]
  have he₂ : (a ≫ j₁) ≫ pullback.snd π.hom π.hom = pullback.snd ψ ψ ≫ ι := by simp [a, j₁]
  have hv₁ : pointsMap B S hS _ (pullback.fst ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j) := by
    obtain ⟨x₁, hx₁⟩ := hN ⟨hw₁, ⟨pointsMap B S hS _ (pullback.fst ψ ψ) v, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, he₁]⟩⟩
    exact ⟨x₁, hιinj (by rw [← pointsMap_comp_apply, hx₁, ← pointsMap_comp_apply, he₁,
      pointsMap_comp_apply])⟩
  have hv₂ : pointsMap B S hS _ (pullback.snd ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j) := by
    obtain ⟨x₂, hx₂⟩ := hN ⟨hw₂, ⟨pointsMap B S hS _ (pullback.snd ψ ψ) v, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, he₂]⟩⟩
    exact ⟨x₂, hιinj (by rw [← pointsMap_comp_apply, hx₂, ← pointsMap_comp_apply, he₂,
      pointsMap_comp_apply])⟩
  obtain ⟨k, rfl⟩ := mem_range_pullbackMap_of_mem_range j ψ v hv₁ hv₂
  have hk : k ∈ closure K := by
    rw [hmemb.isInducing.closure_eq_preimage_closure_image,
      hemb.isInducing.closure_eq_preimage_closure_image, ← Set.image_comp, ← pointsMap_comp,
      ← hρ]
    exact hw
  rw [hK.closure_eq] at hk
  exact ⟨k, hk, by rw [hρ, pointsMap_comp_apply]⟩

include hρ₁ hρ₂ hV hU hψ hπ hι h in
/-- **(N4).** Let `b : X ⟶ X₁` be a morphism over `Y` through which `ι` induces `ι₁`, and suppose
no point of the closure of the off-diagonal points of `X₁ ×_Y X₁` has both coordinates in `R`. Let
`N` be a set of points of `X` meeting `V` only in `U₁`, whose points outside `V` map into `R`.
Then for every closed set `K` of points of `U₁ ×_U U₁` off the diagonal, the image of `K` in
`X ×_Y X` is closed among the points with both coordinates in `N`. -/
theorem closure_image_inter_subset_image_of_comp (hj : IsOpenImmersion B S hS j)
    {X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π₁ : X₁ ⟶ Y.1} {b : X.1 ⟶ X₁}
    (hb : b ≫ π₁ = π.hom) {ι₁ : V ⟶ X₁} (hιb : ι ≫ b = ι₁) {R : Set (points B S hS X₁)}
    (hR : ∀ ρ₁ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π₁ π₁,
      ρ₁ ≫ pullback.fst π₁ π₁ = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι₁ →
      ρ₁ ≫ pullback.snd π₁ π₁ = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι₁ →
      ∀ w ∈ closure (pointsMap B S hS _ ρ₁ ''
          (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ),
        pointsMap B S hS (pullback π₁ π₁) (pullback.fst π₁ π₁) w ∈ R →
        pointsMap B S hS (pullback π₁ π₁) (pullback.snd π₁ π₁) w ∈ R → False)
    {N : Set (points B S hS X.1)}
    (hN : N ∩ Set.range (pointsMap B S hS V ι) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι)))
    (hNR : ∀ x ∈ N, x ∉ Set.range (pointsMap B S hS V ι) → pointsMap B S hS _ b x ∈ R)
    {K : Set (points B S hS (pullback (j ≫ ψ) (j ≫ ψ)))} (hK : IsClosed K)
    (hKΔ : Disjoint K (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))) :
    closure (pointsMap B S hS _ ρ '' K) ∩
        (pointsMap B S hS _ (pullback.fst π.hom π.hom) ⁻¹' N ∩
          pointsMap B S hS _ (pullback.snd π.hom π.hom) ⁻¹' N) ⊆
      pointsMap B S hS _ ρ '' K := by
  rintro w ⟨hw, hw₁, hw₂⟩
  by_cases hwV : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈
      Set.range (pointsMap B S hS V ι) ∨
    pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι)
  · exact mem_image_of_mem_closure_image_of_mem_range hρ₁ hρ₂ hV hU hψ hπ hι h hj hN hK hKΔ hw
      hw₁ hw₂ hwV
  · push Not at hwV
    exact (false_of_mem_closure_offDiagonal_of_comp hb (e₂ := j ≫ ι) (by rw [Category.assoc, hιb])
      hR hρ₁ hρ₂ (closure_mono (Set.image_mono fun k hk hkΔ => Set.disjoint_left.1 hKΔ hk hkΔ) hw)
      (hNR _ hw₁ hwV.1) (hNR _ hw₂ hwV.2)).elim

end Chart

section Package

variable {X Y : AlgebraicSpaces B S hS} {π : X ⟶ Y} {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ι : V ⟶ X.1} {ψ : V ⟶ U} {q : U ⟶ Y.1} {j : U₁ ⟶ V}

/-- **The chart of the repaired gluing step of Stacks 0F4B.** Let `π : X ⟶ Y` be proper over a
Noetherian `Y`, `ι : V ⟶ X` an open immersion, `ψ : V ⟶ U` proper with `ψ ≫ q = ι ≫ π`, and
`j : U₁ ⟶ V` an open immersion with `f = j ≫ ψ` étale and an isomorphism over the reduced closed
subspace on a closed set `Z ⊆ |U|`. There are a proper `b : X' ⟶ X` (a composite of three
`V`-admissible blowups), a lift `ι'` of `ι` with `b⁻¹ V = V`, and an open set `N` of points of
`X'` such that

* `N` contains `U₁` and meets `V` only in `U₁`;
* `N` contains the closure of `f⁻¹ Z`;
* for every closed set `K` of points of `U₁ ×_U U₁` off the diagonal, the image of `K` in
  `X' ×_Y X'` is closed among the points with both coordinates in `N`. -/
theorem exists_isProper_offDiagonal_chart (hZ : B.Contains (⊤_ Scheme.{u}))
    (hπ : IsProper B S hS π.hom) (hYN : IsNoetherian B S hS hZ Y.1)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ) (hι : IsOpenImmersion B S hS ι)
    (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom) (hf : IsEtale B S hS (j ≫ ψ))
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ))) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (ι' : V ⟶ X'.1) (N : Set (points B S hS X'.1)),
      IsProper B S hS b.hom ∧ ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      pointsMap B S hS _ b.hom ⁻¹' Set.range (pointsMap B S hS V ι) =
        Set.range (pointsMap B S hS V ι') ∧
      IsOpen N ∧ Set.range (pointsMap B S hS U₁ (j ≫ ι')) ⊆ N ∧
      N ∩ Set.range (pointsMap B S hS V ι') ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι')) ∧
      closure (pointsMap B S hS U₁ (j ≫ ι') '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)) ⊆ N ∧
      ∀ (π' : X' ⟶ Y), b ≫ π = π' →
      ∀ ρ' : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π'.hom π'.hom,
        ρ' ≫ pullback.fst π'.hom π'.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ρ' ≫ pullback.snd π'.hom π'.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ∀ K : Set (points B S hS (pullback (j ≫ ψ) (j ≫ ψ))), IsClosed K →
          Disjoint K (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ)))) →
          closure (pointsMap B S hS _ ρ' '' K) ∩
              (pointsMap B S hS _ (pullback.fst π'.hom π'.hom) ⁻¹' N ∩
                pointsMap B S hS _ (pullback.snd π'.hom π'.hom) ⁻¹' N) ⊆
            pointsMap B S hS _ ρ' '' K := by
  have hXN : IsNoetherian B S hS hZ X.1 := isNoetherian_of_isProper hZ X.2 Y.2 hYN _ hπ
  have hjopen : IsOpen (Set.range (pointsMap B S hS U₁ j)) := by
    rw [← Set.image_univ]; exact isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hj _ isOpen_univ
  have hA₁ := isClosed_image_preimage_of_isIso_fromPreimage hV hU hU₁ hψ j Zs hZs hiso
  -- step R0
  obtain ⟨X₀, b₀, ι₀, hb₀, hι₀, hι₀o, hpre₀, hdisj₀⟩ :=
    exists_isAdmissibleBlowup_disjoint_closure_image hZ hXN hV hι hA₁ hjopen.isClosed_compl
      (Set.disjoint_left.2 fun _ ⟨y, _, hy⟩ h' => h' ⟨y, hy⟩)
  have hπ₀ : IsProper B S hS (b₀ ≫ π).hom :=
    isProper_comp B S hS X₀.2 X.2 Y.2 _ _ (IsAdmissibleBlowup.isProper B S hS hb₀) hπ
  have h₀ : ψ ≫ q = ι₀ ≫ (b₀ ≫ π).hom := by
    rw [h, ← hι₀, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  -- step R1
  obtain ⟨X₁, β₁, ι₁, R, hβ₁, hι₁, hι₁o, hpre₁, hRc, hTR, hR1⟩ :=
    exists_isAdmissibleBlowup_offDiagonal_separated hZ hπ₀ hYN hV hU hU₁ hψ hι₀o hj h₀ hf Zs hZs
      hiso
  have hπ₁ : IsProper B S hS (β₁ ≫ b₀ ≫ π).hom :=
    isProper_comp B S hS X₁.2 X₀.2 Y.2 _ _ (IsAdmissibleBlowup.isProper B S hS hβ₁) hπ₀
  have hX₁N : IsNoetherian B S hS hZ X₁.1 := isNoetherian_of_isProper hZ X₁.2 Y.2 hYN _ hπ₁
  -- step R2
  obtain ⟨X₂, b₂, ι₂, hb₂, hι₂, hι₂o, hpre₂, hdisj₂⟩ :=
    exists_isAdmissibleBlowup_disjoint_closure_boundary hZ hX₁N hV hι₁o isClosed_closure hRc hTR
  have hπ₂ : IsProper B S hS (b₂ ≫ β₁ ≫ b₀ ≫ π).hom :=
    isProper_comp B S hS X₂.2 X₁.2 Y.2 _ _ (IsAdmissibleBlowup.isProper B S hS hb₂) hπ₁
  have : Mono ι₂ := mono_of_presheaf_isOpenImmersion hι₂o
  have hι₂emb : IsOpenEmbedding (pointsMap B S hS V ι₂) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS ι₂)
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hι₂o)
  have hpre : ∀ {Xa Xb : AlgebraicSpaces B S hS} (c : Xa ⟶ Xb) {ιa : V ⟶ Xa.1} {ιb : V ⟶ Xb.1},
      (∀ A : Set (points B S hS V),
        pointsMap B S hS _ c.hom ⁻¹' (pointsMap B S hS V ιb '' A) = pointsMap B S hS V ιa '' A) →
      pointsMap B S hS _ c.hom ⁻¹' Set.range (pointsMap B S hS V ιb) =
        Set.range (pointsMap B S hS V ιa) := by
    intro Xa Xb c ιa ιb hc
    simpa only [Set.image_univ] using hc Set.univ
  have hrange : Set.range (pointsMap B S hS U₁ (j ≫ ι₂)) =
      pointsMap B S hS V ι₂ '' (Set.range (pointsMap B S hS U₁ j))ᶜᶜ := by
    rw [compl_compl, pointsMap_comp, Set.range_comp]
  have hN₁₂ := inter_range_compl_closure_union_closure_eq (R := R) hι₂emb (hpre b₂ hpre₂)
    hjopen.isClosed_compl
  rw [← hrange] at hN₁₂
  refine ⟨X₂, b₂ ≫ β₁ ≫ b₀, ι₂, _, isProper_comp B S hS X₂.2 X₁.2 X.2 _ _
      (IsAdmissibleBlowup.isProper B S hS hb₂)
      (isProper_comp B S hS X₁.2 X₀.2 X.2 _ _ (IsAdmissibleBlowup.isProper B S hS hβ₁)
        (IsAdmissibleBlowup.isProper B S hS hb₀)), ?_, hι₂o, ?_,
    (isClosed_closure.union isClosed_closure).isOpen_compl,
    hN₁₂.symm.subset.trans Set.inter_subset_left, hN₁₂.subset, ?_, ?_⟩
  · simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [reassoc_of% hι₂, reassoc_of% hι₁, hι₀]
  · simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Set.preimage_comp]
    rw [hpre b₀ hpre₀, hpre β₁ hpre₁, hpre b₂ hpre₂]
  · rw [pointsMap_comp, Set.image_comp]
    refine closure_image_subset_compl_closure_union_closure
      (c := pointsMap B S hS _ (b₂.hom ≫ β₁.hom)) (ι₀ := pointsMap B S hS V ι₀)
      (continuous_pointsMap B S hS _)
      (fun a => by rw [← pointsMap_comp_apply, reassoc_of% hι₂, hι₁])
      (fun a => by rw [← pointsMap_comp_apply, hι₂]) hdisj₀ ?_ hdisj₂
    rw [← Set.image_comp, ← pointsMap_comp]
    exact subset_closure
  · intro π' hπ' ρ' h₁ h₂ K hK hKΔ
    subst hπ'
    have hq : ψ ≫ q = ι₂ ≫ ((b₂ ≫ β₁ ≫ b₀) ≫ π).hom := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      rw [h, reassoc_of% hι₂, reassoc_of% hι₁, reassoc_of% hι₀]
    exact closure_image_inter_subset_image_of_comp h₁ h₂ hV hU hψ
      (by simpa only [Category.assoc] using hπ₂.1) hι₂o hq hj (b := b₂.hom)
      (π₁ := β₁.hom ≫ (b₀ ≫ π).hom) rfl hι₂ (hR1 _ rfl) hN₁₂.subset
      (fun x hx hx₂ => mem_of_mem_compl_closure_union_closure (hpre b₂ hpre₂) hx hx₂)
      hK hKΔ

end Package

end AlgebraicGeometry.Space

end

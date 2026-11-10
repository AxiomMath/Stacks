module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocality

/-!
# Ideal sheaves on a space whose points have smallest open neighbourhoods

Let `X` be a locally topologically ringed space in which every point `x` has a smallest open
neighbourhood `D (m x)`, drawn from a family `D` of opens. Then an ideal sheaf on `X` may be given
by an ideal `K i` of the sections over each `D i`, compatible with restriction: the sections over
an open `U` are those whose restriction to `D (m x)` lies in `K (m x)` for every `x ∈ U`. Over a
member `D (m x)` the sections of the resulting ideal sheaf are `K (m x)`.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ofMinimalOpens`: the ideal sheaf.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ofMinimalOpens_ideal`: its sections
  over a smallest neighbourhood.
* `TopologicalRing.isIdealOfDefinition_sup`: the sum of two ideals of definition is one.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isFundamentalSystemOfIdealsOfDefinitionOn_ofMinimalOpens`: a decreasing sequence of such ideal
  sheaves whose ideals over the smallest neighbourhoods are ideals of definition forming a
  neighbourhood basis of zero is a fundamental system of ideals of definition over the
  quasi-compact opens.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

/-- The sum of two ideals of definition is an ideal of definition. -/
theorem TopologicalRing.isIdealOfDefinition_sup {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I J : Ideal R} (hI : IsIdealOfDefinition I)
    (hJ : IsIdealOfDefinition J) : IsIdealOfDefinition (I ⊔ J) := by
  refine ⟨AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := (I ⊔ J).toAddSubgroup)
    (fun _ h => Ideal.mem_sup_left h) hI.1, fun N hN => ?_⟩
  obtain ⟨V, hV, hVN⟩ := exists_nhds_zero_half hN
  obtain ⟨a, ha⟩ := hI.2 V hV
  obtain ⟨b, hb⟩ := hJ.2 V hV
  refine ⟨a + b, fun x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (Ideal.sup_pow_add_le_pow_sup_pow hx)
  exact hVN y (ha hy) z (hb hz)

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

/-- Restricting twice is restricting once. -/
theorem presheaf_map_homOfLE_apply_apply {X : LTRS.{u}} {U V T : Opens X} (h₁ : V ≤ U)
    (h₂ : T ≤ V) (s : (X.presheaf.obj (op U)).α) :
    (X.presheaf.map (homOfLE h₂).op).1 ((X.presheaf.map (homOfLE h₁).op).1 s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).1 s := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).1 s = _
  rw [← X.presheaf.map_comp]
  rfl

variable {X : LTRS.{u}} {ι : Type*} (D : ι → Opens X) (m : X → ι)
  (hmin : ∀ (x : X) (U : Opens X), x ∈ U → D (m x) ≤ U)
  (K : ∀ i, Ideal (X.presheaf.obj (op (D i))).α)

/-- The ideal sheaf whose sections over `U` are those whose restriction to the smallest
neighbourhood `D (m x)` of every point `x ∈ U` lies in `K (m x)`. -/
noncomputable def ofMinimalOpens : IdealSheaf X where
  ideal U := ⨅ (x : X) (hx : x ∈ U),
    Ideal.comap (X.presheaf.map (homOfLE (hmin x U hx)).op).1 (K (m x))
  map_mem := by
    intro U V h s hs
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hs ⊢
    intro x hx
    have := hs x (h hx)
    rwa [presheaf_map_homOfLE_apply_apply]
  mem_of_locally_mem := by
    intro U s hs
    simp only [Submodule.mem_iInf, Ideal.mem_comap]
    intro x hx
    obtain ⟨V, h, hxV, hmem⟩ := hs x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hmem
    have := hmem x hxV
    rwa [presheaf_map_homOfLE_apply_apply] at this

/-- A section over `U` lies in `ofMinimalOpens D m hmin K` if and only if, for every `x ∈ U`, its
restriction to `D (m x)` lies in `K (m x)`. -/
theorem mem_ofMinimalOpens {U : Opens X} {s : (X.presheaf.obj (op U)).α} :
    s ∈ (ofMinimalOpens D m hmin K).ideal U ↔
      ∀ (x : X) (hx : x ∈ U), (X.presheaf.map (homOfLE (hmin x U hx)).op).1 s ∈ K (m x) := by
  simp only [ofMinimalOpens, Submodule.mem_iInf, Ideal.mem_comap]

/-- Over a smallest neighbourhood `D (m x₀)` the sections of `ofMinimalOpens` are `K (m x₀)`,
when the ideals are compatible with restriction. -/
theorem ofMinimalOpens_ideal
    (hK : ∀ i j (h : D j ≤ D i), Ideal.map (X.presheaf.map (homOfLE h).op).1 (K i) ≤ K j)
    (x₀ : X) (hx₀ : x₀ ∈ D (m x₀)) :
    (ofMinimalOpens D m hmin K).ideal (D (m x₀)) = K (m x₀) := by
  ext s
  rw [mem_ofMinimalOpens]
  refine ⟨fun h => ?_, fun h x hx => hK _ _ _ (Ideal.mem_map_of_mem _ h)⟩
  have := h x₀ hx₀
  rwa [show (homOfLE (hmin x₀ (D (m x₀)) hx₀)).op = 𝟙 _ from rfl, X.presheaf.map_id] at this

/-- **A fundamental system from the smallest neighbourhoods.** Let `K λ i`, for `λ : ℕ`, be ideals
of the sections over the smallest neighbourhoods, compatible with restriction, decreasing in `λ`,
ideals of definition, and forming a neighbourhood basis of zero over each `D i`. Then the ideal
sheaves `ofMinimalOpens … (K λ)` form a fundamental system of ideals of definition over the
quasi-compact opens. -/
theorem isFundamentalSystemOfIdealsOfDefinitionOn_ofMinimalOpens
    (hmem : ∀ x : X, x ∈ D (m x))
    (K : ℕ → ∀ i, Ideal (X.presheaf.obj (op (D i))).α)
    (hK : ∀ l i j (h : D j ≤ D i), Ideal.map (X.presheaf.map (homOfLE h).op).1 (K l i) ≤ K l j)
    (hanti : ∀ l l' i, l ≤ l' → K l' i ≤ K l i)
    (hdef : ∀ l i, TopologicalRing.IsIdealOfDefinition (K l i))
    (hbasis : ∀ i, ∀ N ∈ nhds (0 : (X.presheaf.obj (op (D i))).α), ∃ l, (K l i : Set _) ⊆ N) :
    IsFundamentalSystemOfIdealsOfDefinitionOn
      (Set.range fun l => ofMinimalOpens D m hmin (K l)) fun U => IsCompact (U : Set X) := by
  have hideal : ∀ l (x : X), (ofMinimalOpens D m hmin (K l)).ideal (D (m x)) = K l (m x) :=
    fun l x => ofMinimalOpens_ideal D m hmin (K l) (hK l) x (hmem x)
  have hdefU : ∀ l (U : Opens X), IsCompact (U : Set X) →
      TopologicalRing.IsIdealOfDefinition ((ofMinimalOpens D m hmin (K l)).ideal U) := by
    intro l U hU
    refine (ofMinimalOpens D m hmin (K l)).isIdealOfDefinition_of_isCompact U hU fun x hx => ?_
    exact ⟨D (m x), hmin x U hx, hmem x, by rw [hideal]; exact hdef l (m x)⟩
  refine ⟨?_, fun U hU => ?_⟩
  · rintro _ ⟨l, rfl⟩ U hU
    exact hdefU l U hU
  · refine hasBasis_ideal_of_isCompact (𝒮 := Set.range fun l => ofMinimalOpens D m hmin (K l))
      ⟨_, ⟨0, rfl⟩⟩ ?_ U hU
      (by rintro _ ⟨l, rfl⟩; exact (hdefU l U hU).1) fun x hx => ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      refine ⟨_, ⟨max a b, rfl⟩, fun W => ⟨?_, ?_⟩⟩ <;>
      · intro s hs
        rw [mem_ofMinimalOpens] at hs ⊢
        exact fun y hy => hanti _ _ _ (by omega) (hs y hy)
    · refine ⟨D (m x), hmin x U hx, hmem x, ⟨fun N => ⟨fun hN => ?_, ?_⟩⟩⟩
      · obtain ⟨l, hl⟩ := hbasis (m x) N hN
        exact ⟨_, ⟨l, rfl⟩, by rw [hideal]; exact hl⟩
      · rintro ⟨_, ⟨l, rfl⟩, hlN⟩
        rw [hideal] at hlN
        exact Filter.mem_of_superset ((hdef l (m x)).1.mem_nhds (Ideal.zero_mem _)) hlN

end AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

end

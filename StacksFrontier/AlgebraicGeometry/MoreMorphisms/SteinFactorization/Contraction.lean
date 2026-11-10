module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstantOnFibres
public import StacksFrontier.Topology.Connected.ContractedLocus

/-!
# Contractions: proper morphisms with `𝒪_Y = c_*𝒪_X`

Let `c : X ⟶ Y` be a proper morphism of schemes which is an isomorphism on the sections over
every open of `Y`, i.e. `𝒪_Y = c_*𝒪_X`. Then `c` is its own Stein factorization, so its fibres
are connected and in particular `c` is surjective.

When `X` is moreover Noetherian with every point closed or generic in an irreducible component
(a curve), the fibres of `c` are the connected components of its contracted locus — the union of
the irreducible components of `X` which `c` maps to points — together with the remaining
singletons. Since a contraction is determined by the points it identifies, two contractions of a
curve with the same contracted locus differ by a unique isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isConnected_preimage_singleton_of_isIso_app`: the fibres of `c`
  are connected.
* `AlgebraicGeometry.Scheme.Hom.surjective_of_isIso_app`: `c` is surjective.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_iso_of_contractedLocus_eq` and
  `Scheme.Hom.existsUnique_iso_of_contractedLocus_eq_of_topologicalKrullDim_le_one`:
  two contractions of a curve with the same contracted locus are uniquely isomorphic under the
  curve.

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (c : X ⟶ Y)

/-- **The fibres of a contraction are connected.** If `c` is proper and an isomorphism on the
sections over every open of the target, then every fibre of `c` is connected. -/
theorem isConnected_preimage_singleton_of_isIso_app [IsProper c]
    (hiso : ∀ U : Y.Opens, IsIso (c.app U)) (y : Y) : _root_.IsConnected (c ⁻¹' {y}) := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsAffine U := hU
  let h := c ∣_ U
  have hΓ : IsIso h.appTop := by
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hiso _)
      (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage c U ⊤)).op).isIso_hom
  have := Stacks.SteinFactorization.isIso_fromNormalization_of_isIso_appTop h hΓ
  have := Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper h
  let p : U := ⟨y, hyU⟩
  obtain ⟨q, hq⟩ := h.fromNormalization.surjective p
  have hpre : h ⁻¹' {p} = h.toNormalization ⁻¹' {q} := by
    ext x
    have hx := congrArg (fun φ : (c ⁻¹ᵁ U).toScheme ⟶ U.toScheme ↦ φ.base x)
      h.toNormalization_fromNormalization
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hx, ← hq]
    exact (ConcreteCategory.bijective_of_isIso h.fromNormalization.base).1.eq_iff
  have hconn : _root_.IsConnected (h ⁻¹' {p}) := by
    rw [hpre]
    exact h.toNormalization.isConnected_preimage_singleton q
  have himage : (c ⁻¹ᵁ U).ι '' (h ⁻¹' {p}) = c ⁻¹' {y} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      have := congrArg (fun φ : (c ⁻¹ᵁ U).toScheme ⟶ Y ↦ φ.base x') (morphismRestrict_ι c U)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← this, Set.mem_singleton_iff.1 hx']
      rfl
    · intro hx
      have hxU : x ∈ c ⁻¹ᵁ U := by
        change c x ∈ U
        rw [Set.mem_singleton_iff.1 hx]
        exact hyU
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      have := congrArg (fun φ : (c ⁻¹ᵁ U).toScheme ⟶ Y ↦ φ.base ⟨x, hxU⟩)
        (morphismRestrict_ι c U)
      simp only [Scheme.Hom.comp_base] at this
      refine Set.mem_singleton_iff.2 (Subtype.ext ?_)
      exact this.trans (Set.mem_singleton_iff.1 hx)
  rw [← himage]
  exact hconn.image _ (c ⁻¹ᵁ U).ι.continuous.continuousOn

/-- A proper morphism which is an isomorphism on the sections over every open of the target is
surjective. -/
theorem surjective_of_isIso_app [IsProper c] (hiso : ∀ U : Y.Opens, IsIso (c.app U)) :
    Surjective c :=
  ⟨fun y ↦ (c.isConnected_preimage_singleton_of_isIso_app hiso y).nonempty⟩

/-- **A contraction of a curve is determined by its contracted locus.** Let `X` be a Noetherian
scheme in which every point is closed or the generic point of an irreducible component, and let
`c₁ : X ⟶ Y₁`, `c₂ : X ⟶ Y₂` be proper morphisms which are isomorphisms on all sections. If
`c₁` and `c₂` contract the same irreducible components of `X`, there is a unique isomorphism
`e : Y₁ ≅ Y₂` with `c₁ ≫ e.hom = c₂`. -/
theorem existsUnique_iso_of_contractedLocus_eq [NoetherianSpace X]
    (hdim : ∀ x : X, IsClosed ({x} : Set X) ∨ closure {x} ∈ irreducibleComponents X)
    {Y₁ Y₂ : Scheme.{u}} (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) [IsProper c₁] [IsProper c₂]
    (hiso₁ : ∀ U : Y₁.Opens, IsIso (c₁.app U)) (hiso₂ : ∀ U : Y₂.Opens, IsIso (c₂.app U))
    (h : contractedLocus c₁.base = contractedLocus c₂.base) :
    ∃! e : Y₁ ≅ Y₂, c₁ ≫ e.hom = c₂ := by
  have := c₁.surjective_of_isIso_app hiso₁
  have := c₂.surjective_of_isIso_app hiso₂
  refine existsUnique_iso_of_fibres_eq c₁ c₂ c₁.isClosedMap c₂.isClosedMap hiso₁ hiso₂ ?_
  exact apply_eq_apply_iff_of_contractedLocus_eq hdim c₁.continuous c₁.isClosedMap
    (fun y ↦ (c₁.isConnected_preimage_singleton_of_isIso_app hiso₁ y).isPreconnected)
    c₂.continuous c₂.isClosedMap
    (fun y ↦ (c₂.isConnected_preimage_singleton_of_isIso_app hiso₂ y).isPreconnected) h

/-- **A contraction of a curve is determined by its contracted locus**, for `X` Noetherian of
dimension at most one. -/
theorem existsUnique_iso_of_contractedLocus_eq_of_topologicalKrullDim_le_one [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {Y₁ Y₂ : Scheme.{u}} (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    [IsProper c₁] [IsProper c₂] (hiso₁ : ∀ U : Y₁.Opens, IsIso (c₁.app U))
    (hiso₂ : ∀ U : Y₂.Opens, IsIso (c₂.app U))
    (h : contractedLocus c₁.base = contractedLocus c₂.base) :
    ∃! e : Y₁ ≅ Y₂, c₁ ≫ e.hom = c₂ :=
  existsUnique_iso_of_contractedLocus_eq
    (isClosed_singleton_or_closure_mem_irreducibleComponents hdim) c₁ c₂ hiso₁ hiso₂ h

end AlgebraicGeometry.Scheme.Hom

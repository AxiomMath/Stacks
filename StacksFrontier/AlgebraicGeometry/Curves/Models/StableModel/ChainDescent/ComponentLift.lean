module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# Lifting one-dimensional components along a surjective closed morphism

Let `c : X ⟶ Y` be a surjective morphism of schemes which is a closed map, with `X` of dimension
at most one. Every one-dimensional irreducible component `E₁` of `Y` is dominated by a
one-dimensional irreducible component `E` of `X`: a point of `X` over the generic point `ζ₁` of
`E₁` lies on an irreducible component of `X` whose generic point `η` specializes to it, so
`c(η) = ζ₁`; the image `c(closure {η})` is closed, hence contains `E₁`, which has a point other
than `ζ₁`, so `closure {η}` has a point other than `η` and is one-dimensional. The restriction of
`c` to the reduced components is a non-constant morphism `E ⟶ E₁`.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.exists_reducedComponent_hom_of_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-- The image of the reduced component `ζ` in `X` is the closure of `ζ`. -/
private theorem range_reducedComponentι_base (X : Scheme.{u}) (ζ : genericPointsOne X) :
    Set.range (reducedComponentι X ζ).base = closure ({ζ.1} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **One-dimensional components lift along a surjective closed morphism.** Let `c : X ⟶ Y` be a
surjective morphism of schemes which is a closed map, `X` of dimension at most one. For every
one-dimensional component `ζ₁` of `Y` there are a one-dimensional component `ζ` of `X` and a
non-constant morphism `g` of reduced components with `g ≫ ι_{ζ₁} = ι_ζ ≫ c`. -/
theorem exists_reducedComponent_hom_of_surjective {X Y : Scheme.{u}} (c : X ⟶ Y)
    (hcl : IsClosedMap c.base) (hsurj : Function.Surjective c.base)
    (hX : topologicalKrullDim X ≤ 1) (ζ₁ : genericPointsOne Y) :
    ∃ (ζ : genericPointsOne X) (g : reducedComponent X ζ ⟶ reducedComponent Y ζ₁),
      g ≫ reducedComponentι Y ζ₁ = reducedComponentι X ζ ≫ c ∧
        ¬ ∃ y : reducedComponent Y ζ₁, ∀ x : reducedComponent X ζ, g.base x = y := by
  obtain ⟨x, hx⟩ := hsurj ζ₁.1
  -- the generic point `η` of an irreducible component through `x`
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  set η := hirr.genericPoint with hηdef
  have hη : closure ({η} : Set X) = irreducibleComponent x := by
    have h := hirr.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents x)).closure_eq] at h
  have hηx : η ⤳ x := specializes_iff_mem_closure.mpr (hη ▸ mem_irreducibleComponent)
  -- `c η = ζ₁`
  have hcη : c.base η = ζ₁.1 := by
    have h₁ : c.base η ⤳ ζ₁.1 := hx ▸ hηx.map c.base.hom.continuous
    have h₂ : ζ₁.1 ⤳ c.base η :=
      Scheme.le_iff_specializes.mp (isMax_of_mem_genericPoints ζ₁.1
        (mem_genericPointsOne_iff.mp ζ₁.2).1 (Scheme.le_iff_specializes.mpr h₁))
    exact (h₁.antisymm h₂).eq
  -- a point `y ≠ ζ₁` of `closure {ζ₁}`
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ closure ({ζ₁.1} : Set Y), y ≠ ζ₁.1 := by
    by_contra hcon
    push Not at hcon
    have : Nonempty (closure ({ζ₁.1} : Set Y)) := ⟨⟨ζ₁.1, subset_closure rfl⟩⟩
    have : Subsingleton (closure ({ζ₁.1} : Set Y)) :=
      ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    have h0 := (mem_genericPointsOne_iff.mp ζ₁.2).2
    rw [topologicalKrullDim_eq_zero_of_subsingleton] at h0
    exact zero_ne_one h0
  -- `c (closure {η}) ⊇ closure {ζ₁}`
  have himg : closure ({ζ₁.1} : Set Y) ⊆ c.base '' closure ({η} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨η, subset_closure rfl, hcη⟩)
      (hcl _ isClosed_closure)
  obtain ⟨x', hx'η, hx'y⟩ := himg hy
  have hx'ne : x' ≠ η := fun h => hyne (by rw [← hx'y, h, hcη])
  -- `closure {η}` is one-dimensional
  have hdim : topologicalKrullDim (closure ({η} : Set X)) = 1 := by
    refine le_antisymm (IsInducing.subtypeVal.topologicalKrullDim_le.trans hX) ?_
    have hs : (⟨η, subset_closure rfl⟩ : closure ({η} : Set X)) ⤳ ⟨x', hx'η⟩ :=
      IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hx'η)
    exact one_le_topologicalKrullDim_of_specializes_of_ne hs fun h =>
      hx'ne (congrArg Subtype.val h).symm
  let ζ : genericPointsOne X := ⟨η, mem_genericPointsOne_iff.mpr ⟨by
    change closure ({η} : Set X) ∈ irreducibleComponents X
    rw [hη]
    exact irreducibleComponent_mem_irreducibleComponents x, hdim⟩⟩
  -- the factorization
  let Z₁ : Closeds Y := ⟨closure ({ζ₁.1} : Set Y), isClosed_closure⟩
  have hrange : ∀ p : reducedComponent X ζ, (reducedComponentι X ζ).base p ∈
      closure ({η} : Set X) := by
    intro p
    exact (range_reducedComponentι_base X ζ).subset (Set.mem_range_self p)
  have hsub : Set.range (reducedComponentι X ζ ≫ c).base ⊆ (Z₁ : Set Y) := by
    rintro _ ⟨p, rfl⟩
    have h := image_closure_subset_closure_image c.base.hom.continuous
      ⟨_, hrange p, rfl⟩
    rwa [Set.image_singleton, hcη] at h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z₁ ≤ (reducedComponentι X ζ ≫ c).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.mpr hsub)
  let g : reducedComponent X ζ ⟶ reducedComponent Y ζ₁ :=
    IsClosedImmersion.lift (reducedComponentι Y ζ₁) (reducedComponentι X ζ ≫ c)
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])
  have hg : g ≫ reducedComponentι Y ζ₁ = reducedComponentι X ζ ≫ c :=
    IsClosedImmersion.lift_fac _ _ _
  refine ⟨ζ, g, hg, ?_⟩
  rintro ⟨q, hq⟩
  have hval : ∀ p : reducedComponent X ζ,
      (reducedComponentι Y ζ₁).base (g.base p) = c.base ((reducedComponentι X ζ).base p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  have hmem : ∀ z ∈ closure ({η} : Set X), ∃ p, (reducedComponentι X ζ).base p = z := by
    intro z hz
    exact (range_reducedComponentι_base X ζ).superset hz
  obtain ⟨p₀, hp₀⟩ := hmem η (subset_closure rfl)
  obtain ⟨p₁, hp₁⟩ := hmem x' hx'η
  have h₀ := hval p₀
  have h₁ := hval p₁
  rw [hq, hp₀, hcη] at h₀
  rw [hq, hp₁, hx'y] at h₁
  exact hyne (h₁.symm.trans h₀)

/-- A morphism `g` of reduced components lying over `c` maps the component `closure {ζ}` of `X`
into the component `closure {ζ₁}` of `Y`. -/
theorem mem_closure_of_reducedComponent_hom {X Y : Scheme.{u}} (c : X ⟶ Y)
    {ζ : genericPointsOne X} {ζ₁ : genericPointsOne Y}
    (g : reducedComponent X ζ ⟶ reducedComponent Y ζ₁)
    (hg : g ≫ reducedComponentι Y ζ₁ = reducedComponentι X ζ ≫ c) {x : X}
    (hx : x ∈ closure ({ζ.1} : Set X)) : c.base x ∈ closure ({ζ₁.1} : Set Y) := by
  obtain ⟨p, rfl⟩ := (range_reducedComponentι_base X ζ).superset hx
  have h := (range_reducedComponentι_base Y ζ₁).subset
    (Set.mem_range_self (g.base p))
  rwa [← Scheme.Hom.comp_apply, ← hg, Scheme.Hom.comp_apply]

/-- If a morphism `g` of reduced components lying over `c` is not constant, then `c` is not
constant on the component `closure {ζ}` of `X`. -/
theorem not_exists_forall_eq_of_reducedComponent_hom {X Y : Scheme.{u}} (c : X ⟶ Y)
    {ζ : genericPointsOne X} {ζ₁ : genericPointsOne Y}
    (g : reducedComponent X ζ ⟶ reducedComponent Y ζ₁)
    (hg : g ≫ reducedComponentι Y ζ₁ = reducedComponentι X ζ ≫ c)
    (hnc : ¬ ∃ y : reducedComponent Y ζ₁, ∀ x : reducedComponent X ζ, g.base x = y) :
    ¬ ∃ y : Y, ∀ x ∈ closure ({ζ.1} : Set X), c.base x = y := by
  rintro ⟨y, hy⟩
  have := isIntegral_reducedComponent X ζ
  obtain ⟨p₀⟩ : Nonempty (reducedComponent X ζ) := inferInstance
  have hmem : ∀ p : reducedComponent X ζ, (reducedComponentι X ζ).base p ∈
      closure ({ζ.1} : Set X) := by
    intro p
    exact (range_reducedComponentι_base X ζ).subset (Set.mem_range_self p)
  refine hnc ⟨g.base p₀, fun p => (reducedComponentι Y ζ₁).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply, hy _ (hmem p), hy _ (hmem p₀)]

end Stacks.AlgebraicGeometry.ComponentDegrees

end

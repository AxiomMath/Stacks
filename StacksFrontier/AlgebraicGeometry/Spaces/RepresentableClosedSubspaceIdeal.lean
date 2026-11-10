module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Closed subspaces of a representable algebraic space are closed subschemes

Let `V` be an object of the big fppf site over a scheme `S`.  A closed subspace of the algebraic
space `h_V` represented by `V` is the range of a closed immersion `j : R ⟶ V` of the site
(`AlgebraicGeometry.Space.exists_closedImmersion_range`), and conversely every such range is a
closed subspace (`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`).  This file turns
that pair of statements into a usable dictionary between the closed subspaces of `h_V` and the
quasi-coherent sheaves of ideals on the scheme underlying `V`, and reads the two constructions
of Definition 0CYZ through it: the scheme-theoretic intersection of two closed subspaces of `h_V`
is cut out by the *sum* of the two ideals, and the scheme-theoretic union by their
*intersection*.

The dictionary is a single membership criterion: a point `k : a ⟶ V` of `h_V` lies in the range
of `j` exactly when the ideal sheaf of `j` is contained in the kernel of `k`
(`AlgebraicGeometry.Space.mem_range_yoneda_map_iff`).  One direction is that precomposition
enlarges a kernel, the other is the universal property of a closed immersion in the shape
`AlgebraicGeometry.Space.exists_comp_eq_of_ker_le` gives it.  Everything else follows by lattice
algebra on ideal sheaves: containment of ranges is reverse containment of ideals, membership in an
intersection of ranges is a pair of containments and so a containment of the sum, and the range
cut out by the intersection of two ideals is the smallest closed subspace containing both ranges
because every competitor is itself a range.

## Main results

* `AlgebraicGeometry.Space.mono_yoneda_map_of_mono_toScheme_map`: the Yoneda image of a
  morphism of the site which is a monomorphism of schemes is a monomorphism.
* `AlgebraicGeometry.Space.ker_le_of_mem_range_yoneda_map` and
  `AlgebraicGeometry.Space.mem_range_yoneda_map_iff`: the membership criterion, and its half that
  needs no hypothesis on the morphism.
* `AlgebraicGeometry.Space.range_yoneda_map_le_iff_ker_le`: containment of two ranges is reverse
  containment of the two ideal sheaves.
* `AlgebraicGeometry.Space.exists_closedImmersion_ker_eq`: every quasi-coherent sheaf of ideals
  on the scheme underlying `V` is the ideal sheaf of a closed immersion of the site into `V`.
* `AlgebraicGeometry.Space.range_yoneda_map_inf_eq`: **the scheme-theoretic intersection** of two
  closed subspaces of `h_V` is cut out by the sum of their ideal sheaves.
* `AlgebraicGeometry.Space.schemeTheoreticUnion_eq_range_yoneda_map`: **the scheme-theoretic
  union** of two closed subspaces of `h_V` is cut out by the intersection of their ideal sheaves.

## Implementation notes

The ideal sheaf attached to a closed immersion is Mathlib's `AlgebraicGeometry.Scheme.Hom.ker`,
and the closed subscheme attached to a sheaf of ideals is
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`.  The two are mutually inverse by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` and by the fact that a closed immersion
is isomorphic to the inclusion of its scheme-theoretic image; only the first of these is needed
here, because `AlgebraicGeometry.Space.exists_closedImmersion_ker_eq` produces the closed
immersion of the site from the subscheme rather than recognising a given one.

Nothing in this file is stated through a chosen ideal sheaf of a closed subspace: a closed
subspace determines its ideal only after a presentation as a range has been chosen, so the
statements take the closed immersions as data and the ideals as derived from them.  That keeps
every result free of choice, and it is the form the consumers need, since they have to produce
the closed immersions anyway in order to reach the scheme-level pushout.

## References

* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category over `S` whose underlying morphism of schemes is a
monomorphism has monomorphic Yoneda image.**

Such a morphism is itself a monomorphism, because a morphism of the site is determined by the
underlying morphism of schemes; the Yoneda embedding then preserves it. -/
theorem mono_yoneda_map_of_mono_toScheme_map {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : Mono ((BigFppfOver.toScheme B S hS).map j)) : Mono (yoneda.map j) := by
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map hj
  infer_instance

/-- **The ideal sheaf of a morphism of the site is contained in the kernel of every point of its
range.**  A point in the range is a composite `ψ ≫ j`, and precomposition only enlarges a kernel
sheaf.  No hypothesis on `j` is needed for this half. -/
theorem ker_le_of_mem_range_yoneda_map {R V : BigFppfOver B S hS} (j : R ⟶ V)
    {T : (BigFppfOver B S hS)ᵒᵖ} (k : (yoneda.obj V).obj T)
    (hk : k ∈ (Subfunctor.range (yoneda.map j)).obj T) :
    ((BigFppfOver.toScheme B S hS).map j).ker ≤
      ((BigFppfOver.toScheme B S hS).map k).ker := by
  obtain ⟨ψ, rfl⟩ := hk
  change ((BigFppfOver.toScheme B S hS).map j).ker ≤
      ((BigFppfOver.toScheme B S hS).map (ψ ≫ j)).ker
  rw [Functor.map_comp]
  exact Scheme.Hom.le_ker_comp _ _

/-- **A point of `h_V` lies in the range of a closed immersion `j` of the site exactly when the
ideal sheaf of `j` is contained in its kernel.**

One direction is `AlgebraicGeometry.Space.ker_le_of_mem_range_yoneda_map`.  Conversely a point
whose kernel contains the ideal sheaf of `j` factors through `j` by the universal property of a
closed immersion, `AlgebraicGeometry.Space.exists_comp_eq_of_ker_le`. -/
theorem mem_range_yoneda_map_iff {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
    {T : (BigFppfOver B S hS)ᵒᵖ} (k : (yoneda.obj V).obj T) :
    k ∈ (Subfunctor.range (yoneda.map j)).obj T ↔
      ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map k).ker := by
  refine ⟨ker_le_of_mem_range_yoneda_map B S hS j k, fun hle => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le B S hS j k hj hle
  exact ⟨ψ, hψ⟩

/-- **Containment of the ranges of two closed immersions of the site is reverse containment of
their ideal sheaves.**

For the forward direction the identity of the source exhibits `j'` itself as a point of its own
range, which must then be a point of the range of `j`.  The other direction is the membership
criterion applied to an arbitrary point. -/
theorem range_yoneda_map_le_iff_ker_le {R R' V : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    Subfunctor.range (yoneda.map j') ≤ Subfunctor.range (yoneda.map j) ↔
      ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map j').ker := by
  refine ⟨fun hle => (mem_range_yoneda_map_iff B S hS j hj (T := op R') j').1
    (hle _ ⟨𝟙 R', Category.id_comp j'⟩), fun hle T k hk => ?_⟩
  exact (mem_range_yoneda_map_iff B S hS j hj k).2
    (hle.trans (ker_le_of_mem_range_yoneda_map B S hS j' k hk))

/-- **Every quasi-coherent sheaf of ideals on the scheme underlying an object `V` of the site is
the ideal sheaf of a closed immersion of the site into `V`.**

The closed subscheme it cuts out is a monomorphism into the scheme underlying `V`, hence lies in
the site by `AlgebraicGeometry.exists_mono_bigFppfOver`, and its ideal sheaf is the given one by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`. -/
theorem exists_closedImmersion_ker_eq (V : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData) :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ V),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        ((BigFppfOver.toScheme B S hS).map j).ker = K := by
  obtain ⟨R, g, ε, hε⟩ := exists_mono_bigFppfOver V K.subschemeι inferInstance
  refine ⟨R, g, ?_, ?_⟩
  · rw [← hε]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) ε.hom K.subschemeι).2 inferInstance
  · rw [← hε, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- **The scheme-theoretic intersection of two closed subspaces of a representable algebraic
space is cut out by the sum of their ideal sheaves.**

The intersection of two subfunctors is formed objectwise, so a point lies in it exactly when it
lies in both ranges; by the membership criterion that is a pair of containments of ideal sheaves
in its kernel, which is one containment of their sum. -/
@[sga "3 VIII 6.4" "Binary case"]
theorem range_yoneda_map_inf_eq {R₁ R₂ R₃ V : BigFppfOver B S hS}
    (j₁ : R₁ ⟶ V) (j₂ : R₂ ⟶ V) (j₃ : R₃ ⟶ V)
    (hj₁ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₁))
    (hj₂ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₂))
    (hj₃ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₃))
    (hker : ((BigFppfOver.toScheme B S hS).map j₃).ker =
      ((BigFppfOver.toScheme B S hS).map j₁).ker ⊔
        ((BigFppfOver.toScheme B S hS).map j₂).ker) :
    Subfunctor.range (yoneda.map j₁) ⊓ Subfunctor.range (yoneda.map j₂) =
      Subfunctor.range (yoneda.map j₃) := by
  refine le_antisymm (fun T k hk => ?_) (fun T k hk => ?_)
  · refine (mem_range_yoneda_map_iff B S hS j₃ hj₃ k).2 ?_
    rw [hker, sup_le_iff]
    exact ⟨(mem_range_yoneda_map_iff B S hS j₁ hj₁ k).1 hk.1,
      (mem_range_yoneda_map_iff B S hS j₂ hj₂ k).1 hk.2⟩
  · have hle := (mem_range_yoneda_map_iff B S hS j₃ hj₃ k).1 hk
    rw [hker, sup_le_iff] at hle
    exact ⟨(mem_range_yoneda_map_iff B S hS j₁ hj₁ k).2 hle.1,
      (mem_range_yoneda_map_iff B S hS j₂ hj₂ k).2 hle.2⟩

/-- **The scheme-theoretic union of two closed subspaces of a representable algebraic space is
cut out by the intersection of their ideal sheaves.**

The range cut out by the intersection of the two ideal sheaves is a closed subspace containing
both of the given ones, so the union — the smallest such — is contained in it.  Conversely every
closed subspace of a representable algebraic space is itself the range of a closed immersion of
the site, `AlgebraicGeometry.Space.exists_closedImmersion_range`; one containing both given
subspaces therefore has an ideal sheaf contained in both of theirs, hence in their intersection,
hence contains the range cut out by that intersection. -/
theorem schemeTheoreticUnion_eq_range_yoneda_map {R₁ R₂ R₃ V : BigFppfOver B S hS}
    (j₁ : R₁ ⟶ V) (j₂ : R₂ ⟶ V) (j₃ : R₃ ⟶ V)
    (hj₁ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₁))
    (hj₂ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₂))
    (hj₃ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₃))
    (hker : ((BigFppfOver.toScheme B S hS).map j₃).ker =
      ((BigFppfOver.toScheme B S hS).map j₁).ker ⊓
        ((BigFppfOver.toScheme B S hS).map j₂).ker) :
    (schemeTheoreticUnion B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
        ⟨Subfunctor.range (yoneda.map j₁), isClosedSubspace_range_yoneda_map B S hS j₁ hj₁⟩
        ⟨Subfunctor.range (yoneda.map j₂),
          isClosedSubspace_range_yoneda_map B S hS j₂ hj₂⟩).1 =
      Subfunctor.range (yoneda.map j₃) := by
  have hmem₁ : Subfunctor.range (yoneda.map j₁) ≤ Subfunctor.range (yoneda.map j₃) :=
    (range_yoneda_map_le_iff_ker_le B S hS j₃ j₁ hj₃).2 (hker ▸ inf_le_left)
  have hmem₂ : Subfunctor.range (yoneda.map j₂) ≤ Subfunctor.range (yoneda.map j₃) :=
    (range_yoneda_map_le_iff_ker_le B S hS j₃ j₂ hj₃).2 (hker ▸ inf_le_right)
  refine le_antisymm
    (sInf_le ⟨isClosedSubspace_range_yoneda_map B S hS j₃ hj₃, hmem₁, hmem₂⟩)
    (le_sInf ?_)
  rintro W ⟨hW, hW₁, hW₂⟩
  obtain ⟨RW, jW, hjW, rfl⟩ := exists_closedImmersion_range B S hS W hW
  refine (range_yoneda_map_le_iff_ker_le B S hS jW j₃ hjW).2 ?_
  rw [hker, le_inf_iff]
  exact ⟨(range_yoneda_map_le_iff_ker_le B S hS jW j₁ hjW).1 hW₁,
    (range_yoneda_map_le_iff_ker_le B S hS jW j₂ hjW).1 hW₂⟩

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedImmersionCoborderLift

/-!
# The ambient pair of a commutative square of immersions of schemes of the site

Let
```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B` whose two horizontal morphisms are immersions of schemes.  The proof of part (2) of
[Stacks Project, Tag 04G2] — and of [Stacks Project, Tag 04CP] in the source — replaces `V` and
`V'` by open subschemes on which `j` and `j'` become **closed** immersions and which `a` carries
one into the other.  This file constructs that pair, together with the closed factorisations and
the commutativity of the resulting square.

For `V'` the canonical choice works: `AlgebraicGeometry.Space.immersionCoborderObj` at `j'`, whose
closed factorisation is `AlgebraicGeometry.Space.immersionCoborderLift`.  For `V` it does not —
`a` need not carry the coborder of the range of `j` into the coborder of the range of `j'`; for a
closed immersion `j` the former is all of `V`, and `a` can land outside the latter.  The ambient
built here is therefore smaller, and it is built in **two** steps from results of the library rather
than by cutting `j.coborderRange` down and proving the restriction closed by hand:

* first the open `a⁻¹ᵁ (j').coborderRange` of `V`, which contains the range of `j` **because the
  square commutes**, so that `AlgebraicGeometry.Space.openSubLift` factors `j` through it; that
  factorisation is again an immersion, by cancellation along the inclusion of the open;
* then the canonical coborder ambient of *that* factorisation, so that the closed factorisation
  is `AlgebraicGeometry.Space.immersionCoborderLift` and its closedness is the existing
  instance rather than a restriction argument.

The morphism of ambients is `AlgebraicGeometry.Space.openSubMap` at the pair
`a⁻¹ᵁ (j').coborderRange ≤ a⁻¹ᵁ (j').coborderRange`, whose hypothesis is `le_rfl`, preceded by the
inclusion of the coborder ambient of the intermediate factorisation.

## Main definitions

* `AlgebraicGeometry.Space.squareAmbientPreObj` and
  `AlgebraicGeometry.Space.squareAmbientPreLift`: the intermediate open `a⁻¹ᵁ (j').coborderRange`
  and the factorisation of `j` through it.
* `AlgebraicGeometry.Space.squareAmbientObj` and `AlgebraicGeometry.Space.squareAmbientLift`: the
  ambient of `V` and the **closed** factorisation of `j` through it.
* `AlgebraicGeometry.Space.squareAmbientMap`: the morphism of ambients
  `AlgebraicGeometry.Space.squareAmbientObj ⟶ AlgebraicGeometry.Space.immersionCoborderObj` at
  `j'`.

## Main results

* `AlgebraicGeometry.Space.isImmersion_toScheme_map_openSubLift`: the factorisation of an
  immersion through an open containing its range is an immersion.  This is
  `AlgebraicGeometry.IsImmersion.of_comp` along `AlgebraicGeometry.Space.openLiftScheme_comp_ι`,
  and nothing in the tree stated it for `AlgebraicGeometry.Space.openSubLift`.
* `AlgebraicGeometry.Space.range_subset_preimage_coborderRange`: the range containment that the
  intermediate factorisation needs, and the only place the commutativity of the square is used.
* `AlgebraicGeometry.Space.squareAmbientLift_comp_squareAmbientHom`: the ambient factorisation of
  `j`.
* `AlgebraicGeometry.Space.squareAmbientLift_comp_squareAmbientMap`: **the square of closed
  immersions**, proved by cancelling the monomorphism
  `AlgebraicGeometry.Space.openSubHom` of the ambient of `j'`.

No `@[stacks]` attribute is claimed: this is the construction the source's proof makes, not a
statement of the tag.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The factorisation of an immersion through an open containing its range is an immersion.**
It is `AlgebraicGeometry.IsImmersion.of_comp` applied along
`AlgebraicGeometry.Space.openLiftScheme_comp_ι`, the inclusion of the open needing no hypothesis
of its own. -/
instance isImmersion_toScheme_map_openSubLift {A A' : BigFppfOver B S hS} (a : A' ⟶ A)
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map a)]
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) :
    AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubLift A O a ha)) := by
  have hr : Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ (O : Set _) := by
    rintro _ ⟨y, rfl⟩
    exact ha y
  have h : AlgebraicGeometry.IsImmersion (openLiftScheme a O hr ≫ O.ι) := by
    rw [openLiftScheme_comp_ι]
    infer_instance
  rw [toScheme_map_openSubLift]
  exact AlgebraicGeometry.IsImmersion.of_comp (openLiftScheme a O hr) O.ι

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

omit hj in
/-- **The range of `j` lies in the preimage along `a` of the coborder ambient of `j'`.**  This is
the only place the commutativity of the square is used: a point of the range of `j` is carried by
`a` to a point of the range of `j'`, which lies in the coborder of that range. -/
theorem range_subset_preimage_coborderRange (hsq : j ≫ a = b ≫ j') :
    Set.range ⇑((BigFppfOver.toScheme B S hS).map j) ⊆
      (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map j').coborderRange : Set _) := by
  rw [Set.range_subset_iff]
  intro y
  have hc : (BigFppfOver.toScheme B S hS).map j ≫ (BigFppfOver.toScheme B S hS).map a =
      (BigFppfOver.toScheme B S hS).map b ≫ (BigFppfOver.toScheme B S hS).map j' := by
    rw [← Functor.map_comp, ← Functor.map_comp, hsq]
  have hy := congrArg (fun f : (BigFppfOver.toScheme B S hS).obj R ⟶
    (BigFppfOver.toScheme B S hS).obj V' ↦ f.base y) hc
  change ((BigFppfOver.toScheme B S hS).map a).base
      (((BigFppfOver.toScheme B S hS).map j).base y) ∈
    ((BigFppfOver.toScheme B S hS).map j').coborderRange
  have hpt : ((BigFppfOver.toScheme B S hS).map a).base
        (((BigFppfOver.toScheme B S hS).map j).base y) =
      ((BigFppfOver.toScheme B S hS).map j').base
        (((BigFppfOver.toScheme B S hS).map b).base y) := by
    simpa using hy
  rw [hpt, Scheme.Hom.coborderRange]
  exact subset_coborder (Set.mem_range_self _)

/-- The intermediate ambient: the open `a⁻¹ᵁ (j').coborderRange` of `V`, as an object of the
site. -/
noncomputable abbrev squareAmbientPreObj : BigFppfOver B S hS :=
  openSub V (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
    ((BigFppfOver.toScheme B S hS).map j').coborderRange)

/-- The factorisation of `j` through the intermediate ambient.  An immersion, by
`AlgebraicGeometry.Space.isImmersion_toScheme_map_openSubLift`. -/
noncomputable abbrev squareAmbientPreLift (hsq : j ≫ a = b ≫ j') :
    R ⟶ squareAmbientPreObj B S hS j' a :=
  openSubLift V (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map j').coborderRange) j
    (fun y => range_subset_preimage_coborderRange B S hS j j' b a hsq ⟨y, rfl⟩)

omit hj in
/-- The intermediate factorisation followed by the inclusion of the intermediate ambient is
`j`. -/
theorem squareAmbientPreLift_comp_openSubHom (hsq : j ≫ a = b ≫ j') :
    squareAmbientPreLift B S hS j j' b a hsq ≫
        openSubHom V (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
          ((BigFppfOver.toScheme B S hS).map j').coborderRange) = j :=
  openSubLift_comp_openSubHom _ _ _ _

/-- **The ambient of `V` for the square**: the coborder ambient of the intermediate
factorisation. -/
noncomputable abbrev squareAmbientObj (hsq : j ≫ a = b ≫ j') : BigFppfOver B S hS :=
  immersionCoborderObj B S hS (squareAmbientPreLift B S hS j j' b a hsq)

/-- **The closed factorisation of `j` through the ambient of the square.**  Its morphism of
schemes is a closed immersion by the instance
`AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_immersionCoborderLift`. -/
noncomputable abbrev squareAmbientLift (hsq : j ≫ a = b ≫ j') :
    R ⟶ squareAmbientObj B S hS j j' b a hsq :=
  immersionCoborderLift B S hS (squareAmbientPreLift B S hS j j' b a hsq)

/-- The inclusion of the ambient of the square into `V`. -/
noncomputable def squareAmbientHom (hsq : j ≫ a = b ≫ j') :
    squareAmbientObj B S hS j j' b a hsq ⟶ V :=
  openSubHom (squareAmbientPreObj B S hS j' a)
      ((BigFppfOver.toScheme B S hS).map
        (squareAmbientPreLift B S hS j j' b a hsq)).coborderRange ≫
    openSubHom V (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map j').coborderRange)

/-- **The ambient factorisation of `j`.** -/
theorem squareAmbientLift_comp_squareAmbientHom (hsq : j ≫ a = b ≫ j') :
    squareAmbientLift B S hS j j' b a hsq ≫ squareAmbientHom B S hS j j' b a hsq = j := by
  rw [squareAmbientHom, ← Category.assoc, squareAmbientLift,
    immersionCoborderLift_comp_openSubHom, squareAmbientPreLift_comp_openSubHom]

/-- **The morphism of ambients.**  The inclusion of the coborder ambient of the intermediate
factorisation into the intermediate ambient, followed by the restriction of `a` to the
intermediate ambient, whose target is the coborder ambient of `j'` by construction — the
hypothesis of `AlgebraicGeometry.Space.openSubMap` being `le_rfl` for this pair. -/
noncomputable def squareAmbientMap (hsq : j ≫ a = b ≫ j') :
    squareAmbientObj B S hS j j' b a hsq ⟶ immersionCoborderObj B S hS j' :=
  openSubHom (squareAmbientPreObj B S hS j' a)
      ((BigFppfOver.toScheme B S hS).map
        (squareAmbientPreLift B S hS j j' b a hsq)).coborderRange ≫
    openSubMap a
      (((BigFppfOver.toScheme B S hS).map a) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map j').coborderRange)
      ((BigFppfOver.toScheme B S hS).map j').coborderRange le_rfl

/-- The morphism of ambients followed by the inclusion of the coborder ambient of `j'` is the
inclusion of the ambient of the square followed by `a`. -/
theorem squareAmbientMap_comp_openSubHom (hsq : j ≫ a = b ≫ j') :
    squareAmbientMap B S hS j j' b a hsq ≫
        openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange =
      squareAmbientHom B S hS j j' b a hsq ≫ a := by
  rw [squareAmbientMap, squareAmbientHom, Category.assoc, openSubMap_comp_openSubHom,
    Category.assoc]

/-- **The square of closed immersions.**  Both sides composed with the inclusion of the coborder
ambient of `j'` — a monomorphism by `AlgebraicGeometry.Space.mono_openSubHom_of_opens` — are
`j ≫ a = b ≫ j'`. -/
theorem squareAmbientLift_comp_squareAmbientMap (hsq : j ≫ a = b ≫ j') :
    squareAmbientLift B S hS j j' b a hsq ≫ squareAmbientMap B S hS j j' b a hsq =
      b ≫ immersionCoborderLift B S hS j' := by
  have hmono := mono_openSubHom_of_opens V'
    ((BigFppfOver.toScheme B S hS).map j').coborderRange
  refine (cancel_mono (f := openSubHom V'
    ((BigFppfOver.toScheme B S hS).map j').coborderRange)).1 ?_
  rw [Category.assoc, squareAmbientMap_comp_openSubHom, Category.assoc,
    immersionCoborderLift_comp_openSubHom, ← Category.assoc,
    squareAmbientLift_comp_squareAmbientHom, hsq]

end AlgebraicGeometry.Space

end

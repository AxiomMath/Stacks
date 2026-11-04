module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.SummandSubspaceConormal

/-!
# The summand identification, read at the square of the new pair

Let `Z ⊆ Y ⊆ W` be closed subspaces of an algebraic space over a scheme `S` contained in a big
fppf site `B`, let `X ⊆ X'` be a closed subspace of another algebraic space and let
`(f, g) : (Z ⊆ W) → (X ⊆ X')` be a commutative square of closed subspaces.
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormal.lean` shows that a summand of
`𝒞_{Z/W}` complementary to the inclusion `i^*𝓘_Y ⊆ 𝒞_{Z/W}` of defining ideal sheaves maps
isomorphically onto `𝒞_{j⁻¹(Z)/Y}` along the right-hand map of the conormal complex of the chain.
This file **reads that isomorphism as the canonical map of [Stacks Project, Tag 04CP] attached to
the square `(j⁻¹(Z) ⊆ Y) → (X ⊆ X')`**, in the case where the summand is the canonical map of the
square `(Z ⊆ W) → (X ⊆ X')`.

That is the step the proof of [Stacks Project, Tag 06D8] takes when, having cut `Z'` out of the
universal first order thickening `Z''` by a summand of `𝒞_{Z/X'}`, it records

> Note that by construction `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`

and then feeds that identification to [Stacks Project, Tag 06BH].  In the names of this file `W`
is `Z''`, `Y` is `Z'`, `g : W ⟶ X'` is the structure morphism of the universal thickening and
`f : Z ⟶ X` is the given morphism, so the canonical map of the square `(Z ⊆ W) → (X ⊆ X')` is the
left-hand map `f^*𝒞_{X/X'} ⟶ 𝒞_{Z/X'}` of the conormal sequence of [Stacks Project, Tag 06CC] and
the conclusion is that its complementary summand *is* `𝒞_{Z/Z'}`, through the canonical map of the
square `(Z ⊆ Z') → (X ⊆ X')`.

## Main results

* `AlgebraicGeometry.Space.preimageSubspace_square_comp`: the two squares
  `(j⁻¹(Z) ⊆ Y) → (Z ⊆ W) → (X ⊆ X')` compose, which is the commutativity datum the outer
  rectangle's canonical map consumes.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_modulePullback_comp_conormalMap`: **the
  transport.**  If the inverse image along the projection `p : j⁻¹(Z) ⟶ Z` of the canonical map of
  the square `(Z ⊆ W) → (X ⊆ X')`, followed by the right-hand map
  `p^*𝒞_{Z/W} ⟶ 𝒞_{j⁻¹(Z)/Y}` of the conormal complex of the chain, is an isomorphism, then the
  canonical map of the outer square `(j⁻¹(Z) ⊆ Y) → (X ⊆ X')` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_definingIdealSheafSplitting`: **the identification
  at the configuration of [Stacks Project, Tag 06D8]**, with the splitting as the only hypothesis:
  if `𝒞_{Z/W}` splits as the canonical map of `(Z ⊆ W) → (X ⊆ X')` plus the inverse image of the
  inclusion `𝓘_Y ⊆ 𝓘_Z` of defining ideal sheaves, then the canonical map of
  `(j⁻¹(Z) ⊆ Y) → (X ⊆ X')` is an isomorphism.

## Implementation notes

**The whole content is the composition law.**  `AlgebraicGeometry.Space.conormalMap_comp`, part (3)
of [Stacks Project, Tag 04G2], writes the canonical map of the outer rectangle as the composition
comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU] followed
by exactly the composite that
`AlgebraicGeometry.Space.isIso_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting`
proves invertible, and the comparison is an isomorphism.  Nothing else is used, and in particular
no first-order hypothesis and no pushforward: the scheme-level analogue
`Stacks.Thickenings.isIso_immersionConormalSheafMap_of_isIso_comp_conormalSequenceRightMap` of
`StacksFrontier/AlgebraicGeometry/Thickenings/SummandSubschemeConormal.lean` has in addition to
reconcile the identity pullback with its target, because at the scheme level the lower subscheme
of the new pair is `Z` itself and the left vertical map of the outer rectangle is `𝟙_Z ≫ f`.  Here
it is `p ≫ f` for the projection `p` of the fibre-product square, so the composition law applies on
the nose.

**The subspace of `Y` is the inverse image `j⁻¹(Z)`, not `Z`.**  The right-hand map of the conormal
complex of a chain of closed subspaces is the canonical map of [Stacks Project, Tag 04CP] at the
fibre-product square of [Stacks Project, Tag 083Q], so the conormal module of the new pair is read
on `j⁻¹(Z)` and the statements below are at that spelling.  `Z` itself is a closed subspace of `Y`
by `AlgebraicGeometry.Space.isClosedSubspace_of_le`, [Stacks Project, Tag 02YX]; identifying the
two closed subspaces of `Y`, and their conormal modules, is not done here and not needed for the
transport.

**The commutativity datum is a named theorem.**  `AlgebraicGeometry.Space.conormalMap` takes the
commutativity of its square as an argument, so the statement of the transport has to name one
proof of the composed square; `AlgebraicGeometry.Space.preimageSubspace_square_comp` is that
proof, and it is assembled by `congrArg` and `CategoryTheory.Category.assoc` rather than by `rw`,
because `AlgebraicGeometry.Space.preimageSubspace` and
`AlgebraicGeometry.Space.preimageProjection` are reducible abbreviations while
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` is stated at their unfoldings, so the two
spellings are definitionally but not syntactically equal.

**The inverse image of modules is made irreducible for the transport.**  The composition law
presents the source of the canonical map of the outer rectangle at a different, definitionally
equal, spelling from the one the goal carries, and left reducible the unifier crosses between them
by unfolding `AlgebraicGeometry.Space.modulePullback` inside `CategoryTheory.Functor.obj`
congruence, which exhausts the heartbeat budget — both in
`CategoryTheory.IsIso.comp_isIso'` and in the route through
`CategoryTheory.isIso_of_eq_iso_hom`, which additionally asks `whnf` for the components of a
composite isomorphism.  `attribute [local irreducible] modulePullback` in the section makes the
two functors matched argument by argument instead, and the proof is then immediate.  This is the
device of `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapVanishing.lean` and of the
`Respelling` section of
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormal.lean`.  The attribute is confined to
that section; the packaged statement below is proved with the inverse image reducible again.

## What is not proved

* **No `@[stacks]` attribute is placed.**  These statements are the space-level replacement for one
  sentence inside the proof of [Stacks Project, Tag 06D8].  That tag needs in addition the
  space-level form of the conormal sequence of [Stacks Project, Tag 06CC], which produces the
  splitting, and the closing paragraph, which runs [Stacks Project, Tag 06BH] in the direction
  (2) ⟹ (1) and then [Stacks Project, Tag 06AG]; neither is available.
* **The splitting is a hypothesis.**  Nothing here produces one.  The producers are
  `AlgebraicGeometry.Space.nonempty_splitting_of_shortExact_of_exists_section` and
  `AlgebraicGeometry.Space.nonempty_splitting_of_shortExact_of_exists_retraction` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleSplittingFromSection.lean`.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X' : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS W.1)
    (XX : ClosedSubspaces B S hS X'.1) (g : W ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨XX.1.toFunctor, XX.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS W Z ≫ g = f ≫ subspaceInclusion B S hS X' XX)

/-! ### The composed square -/

include hsq in
/-- **The fibre-product square of `Z` in `Y` composes with a square out of `(Z ⊆ W)`.**  For
closed subspaces `Y, Z ⊆ W`, the inclusion of the inverse image `j⁻¹(Z) ⊆ Y` of `Z` along
`j : Y ⟶ W` followed by `j ≫ g` is the projection `p : j⁻¹(Z) ⟶ Z` followed by `f` and the
inclusion of `X ⊆ X'`.

This is the commutativity of the outer rectangle of the two stacked squares
`(j⁻¹(Z) ⊆ Y) → (Z ⊆ W) → (X ⊆ X')`, the lower one given by `hsq` and the upper one by
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`.  It is the datum that the canonical map
of conormal modules of [Stacks Project, Tag 04CP] of the outer rectangle takes. -/
theorem preimageSubspace_square_comp :
    subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z) ≫
        subspaceInclusion B S hS W Y ≫ g =
      (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f) ≫
        subspaceInclusion B S hS X' XX :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ g)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS W Y) Z)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
            (fun m ↦ preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ m) hsq).trans
          (Category.assoc _ _ _).symm)))

/-! ### The transport -/

section Transport

-- The inverse image of modules carries the source and target of its morphism as implicit
-- arguments, and the two junctions of the composition law present two definitionally equal
-- spellings of them.  Left reducible, the unifier crosses between them by unfolding
-- `AlgebraicGeometry.Space.modulePullback`, which does not finish; made irreducible it matches the
-- functors argument by argument, which is immediate.  This is the device of
-- `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapVanishing.lean`.
attribute [local irreducible] modulePullback

/-- **The summand identification, read at the square of the new pair.**  Let `Z ⊆ Y ⊆ W` be closed
subspaces and let `(f, g) : (Z ⊆ W) → (X ⊆ X')` be a commutative square of closed subspaces.  If
the inverse image along the projection `p : j⁻¹(Z) ⟶ Z` of the canonical map
`f^*𝒞_{X/X'} ⟶ 𝒞_{Z/W}` of [Stacks Project, Tag 04CP] of that square, followed by the canonical
map `p^*𝒞_{Z/W} ⟶ 𝒞_{j⁻¹(Z)/Y}` of the fibre-product square of `Z` along `j : Y ⟶ W`, is an
isomorphism, then the canonical map `(p ≫ f)^*𝒞_{X/X'} ⟶ 𝒞_{j⁻¹(Z)/Y}` of the composed square
`(j⁻¹(Z) ⊆ Y) → (X ⊆ X')` is an isomorphism.

The composite of the two canonical maps is the canonical map of the composed square, up to the
composition comparison of [Stacks Project, Tag 03LU], by
`AlgebraicGeometry.Space.conormalMap_comp`, part (3) of [Stacks Project, Tag 04G2]; the comparison
is an isomorphism. -/
theorem isIso_conormalMap_of_isIso_modulePullback_comp_conormalMap
    (h : IsIso ((modulePullback B S hS
            (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z)).map
          (conormalMap B S hS Z XX g f hsq) ≫
        conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z) Z
          (subspaceInclusion B S hS W Y)
          (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS W Y) Z))) :
    IsIso (conormalMap B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z) XX
      (subspaceInclusion B S hS W Y ≫ g)
      (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f)
      (preimageSubspace_square_comp B S hS Y Z XX g f hsq)) := by
  rw [conormalMap_comp B S hS (subspaceInclusion B S hS W Y) g
    (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z) Z XX
    (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z) f
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS W Y) Z) hsq
    (preimageSubspace_square_comp B S hS Y Z XX g f hsq)]
  exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _) h

end Transport

/-- **The canonical map of the square `(j⁻¹(Z) ⊆ Y) → (X ⊆ X')` is an isomorphism**, for the
closed subspace `Y ⊆ W` whose defining ideal sheaf is a summand of `𝒞_{Z/W}` complementary to the
canonical map of the square `(Z ⊆ W) → (X ⊆ X')`.

The hypotheses are a split decomposition of `𝒞_{Z/W}` whose inclusion is that canonical map and
whose section is the inverse image along `i : Z ⟶ W` of the inclusion `𝓘_Y ⊆ 𝓘_Z` of defining
ideal sheaves — which is what
`AlgebraicGeometry.Space.exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le` of
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceFirstOrderThickening.lean` produces for the
subspace cut out by the other summand.  **Nothing else is assumed**: this is
`AlgebraicGeometry.Space.isIso_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting`,
whose only hypothesis is the splitting, followed by
`AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_modulePullback_comp_conormalMap`.

This is the space-level form of the sentence "by construction `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`" in the
proof of [Stacks Project, Tag 06D8], stated as the invertibility of the canonical map of the
square that the closing paragraph of that proof hands to [Stacks Project, Tag 06BH].  There the
square is written `(Z ⊆ Z') → (X ⊆ X')`; here the lower subspace of the new pair is the inverse
image `j⁻¹(Z) ⊆ Z'` of [Stacks Project, Tag 083Q], for the reason the implementation notes of this
file give. -/
theorem isIso_conormalMap_of_definingIdealSheafSplitting (hZY : Z.1 ≤ Y.1)
    (γ : conormalModule B S hS W Z ⟶
      (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
        (definingIdealSheaf B S hS W Y).toSheafOfModules)
    (hz : conormalMap B S hS Z XX g f hsq ≫ γ = 0)
    (σ : (CategoryTheory.ShortComplex.mk (conormalMap B S hS Z XX g f hsq) γ hz).Splitting)
    (hs : σ.s =
      (show (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
            (definingIdealSheaf B S hS W Y).toSheafOfModules ⟶
          conormalModule B S hS W Z from
        (modulePullback B S hS (subspaceInclusion B S hS W Z)).map
          (definingIdealSheafHomOfLe B S hS Y Z hZY))) :
    IsIso (conormalMap B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z) XX
      (subspaceInclusion B S hS W Y ≫ g)
      (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f)
      (preimageSubspace_square_comp B S hS Y Z XX g f hsq)) :=
  isIso_conormalMap_of_isIso_modulePullback_comp_conormalMap B S hS Y Z XX g f hsq
    (isIso_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting B S hS Y Z hZY
      (conormalMap B S hS Z XX g f hsq) γ hz σ hs)

end AlgebraicGeometry.Space

end

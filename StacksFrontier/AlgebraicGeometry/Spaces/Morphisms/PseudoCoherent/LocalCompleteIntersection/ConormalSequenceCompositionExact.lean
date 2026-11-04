module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalShortExactUnconditional
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalShortExact
-- Not `public`: the middle exactness of the conormal complex of a closed subspace inside the
-- inverse image of a closed subspace is used only in the proof of
-- `AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence` below.
import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequencePreimageExact

/-!
# The conormal sequence of a composition of formally unramified morphisms of spaces is exact

Let `Z ⟶ Y ⟶ X` be formally unramified morphisms of algebraic spaces over a scheme `S`,
presented, as in `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean`
(Stacks 06BF), by universal first-order thickenings `Z ⊂ Z'` over `X` and `Y ⊂ Y'` over `X`, with
`i : Z ⟶ Y` the first morphism.  The conormal sequence

```
  i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0
```

of Stacks 06BD is read, as in `ConormalShortExact.lean` beside this file, on the copy of `Z`
inside the fibre product `Y ×_{Y'} Z'`, along the projection `π` of that copy onto `Z`.  This
file proves, unconditionally, the two clauses of Stacks 06BD that Stacks 06CC refers to as "the
exact sequence of Lemma 06BD", and with them that short exactness of the sequence is exactly
injectivity of its left-hand arrow.

The left-hand arrow is written out as `AlgebraicGeometry.Space.modulePullbackMap` of
`AlgebraicGeometry.Space.universalThickeningCompConormalLowerMap`, `π^*` of the map of
Stacks 04CP at the square `AlgebraicGeometry.Space.universalThickeningComp_subspace_square`,
rather than as `AlgebraicGeometry.Space.universalThickeningCompConormalLeftMap`; the
implementation notes say why.

## Main results

* `AlgebraicGeometry.Space.universalThickeningCompConormalSequence_comp_eq_zero`: **the two
  arrows of the sequence compose to zero.**  By the composition law of part (3) of Stacks 04G2,
  `AlgebraicGeometry.Space.conormalMap_comp`, the composite is the map of Stacks 04CP of the
  outer rectangle, whose lower edge factors through `Y` by the structure morphism of the fibre
  product, so it vanishes by `AlgebraicGeometry.Space.conormalMap_eq_zero_of_factorization`.
* `AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence`: **the sequence is
  exact at `𝒞_{Z/X}`.**  The fibre product `Y ×_{Y'} Z'` presents the copy of `Z` as a closed
  subspace inside the inverse image of a closed subspace downstairs, which is the presentation
  `AlgebraicGeometry.Space.exact_conormalShortComplex_preimage` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequencePreimageExact.lean` states that clause at.
  Together with the previous item it is the middle-exactness assertion of clause (2) of
  Stacks 06BF.
* `AlgebraicGeometry.Space.shortExact_iff_mono_pullback_universalThickeningCompConormalLowerMap`:
  short exactness of the sequence is exactly injectivity of its left-hand arrow, the epimorphism
  at the right term being clause (2) of Stacks 06BF,
  `AlgebraicGeometry.Space.epi_conormalMap_comp`.
* `AlgebraicGeometry.Space.mono_pullback_universalThickeningCompConormalLowerMap_of_chart`:
  that injectivity descends from one étale scheme chart surjective on points.

Injectivity of the left-hand arrow for a local complete intersection morphism, which is what
Stacks 06CC adds over these, is not proved here.

## Implementation notes

**Why the left-hand arrow has no name of its own.**  The vanishing of the composite is read off
the composition law of part (3) of Stacks 04G2 by cancelling an isomorphism, which asks for the
left-hand arrow and the law's middle factor to be recognized as one term.  A `def` whose body is
the inverse image of a map of modules cannot be so recognized: a definition's *value* is run
through Lean's abstraction of nested proofs, so the body stored for it spells the algebraic
spaces and the modules of the inverse image with auxiliary proof constants, while any later
statement writing the same expression out spells them with the proof terms inline.  Identifying
the two is then a comparison of two spellings of one inverse image under
`CategoryTheory.Functor.obj`, which forces `AlgebraicGeometry.Space.modulePullback` open to its
construction by sheafification; that exhausts the elaborator's budget and, with
the reducibility attribute of the section below keeping the elaborator out, to exhaust the
kernel's instead.  A `theorem`'s *type* is not abstracted, so every statement that writes the
arrow out agrees with every other one on the nose.

What *is* named is the data the arrow is built from, at spellings the comparison does reach:
`AlgebraicGeometry.Space.universalThickeningCompConormalLowerMap`, the map of Stacks 04CP at the
square, whose arguments are all algebraic spaces and closed subspaces; and
`AlgebraicGeometry.Space.modulePullbackMap`, the action of the inverse image on morphisms, whose
arguments are all arbitrary, so that its defining equation carries no proof term at all.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD), the sequence.
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF), clause (2).
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the two arrows.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (3), the
  composition law for the map of Stacks 04CP.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image of a map of modules, with its data named -/

/-- **The inverse image of a map of modules along a morphism of algebraic spaces**, with the
morphism and the two modules named as arguments: this is `CategoryTheory.Functor.map` of
`AlgebraicGeometry.Space.modulePullback`.

It is a declaration of its own so that the data of the inverse image are *arguments of the head
symbol*; the implementation notes of this file record what that buys. -/
public noncomputable def modulePullbackMap {U V : AlgebraicSpaces B S hS} (φ : U ⟶ V)
    {M N : Modules.{u, u} B S hS V.1 V.2} (ψ : M ⟶ N) :
    (modulePullback B S hS φ).obj M ⟶ (modulePullback B S hS φ).obj N :=
  (modulePullback B S hS φ).map ψ

/-- `AlgebraicGeometry.Space.modulePullbackMap` is the action of the inverse image functor on
morphisms, which it is by definition.  The morphism and the two modules are arbitrary here, so
neither side of the equation carries a proof term and the equation is structural. -/
public theorem modulePullbackMap_eq {U V : AlgebraicSpaces B S hS} (φ : U ⟶ V)
    {M N : Modules.{u, u} B S hS V.1 V.2} (ψ : M ⟶ N) :
    modulePullbackMap B S hS φ ψ = (modulePullback B S hS φ).map ψ :=
  rfl

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

section Chain

-- Every comparison below is between two spellings of a single inverse image, and settling one
-- forces `AlgebraicGeometry.Space.modulePullback` open to its construction by sheafification,
-- which the heartbeat budget does not survive; none of the comparisons needs it unfolded.
attribute [local irreducible] modulePullback conormalModule

/-- The square of Stacks 04CP formed by the subspace `Z ⊆ Z'`, the subspace `Y ⊆ Y'` and the
morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF: that morphism restricts to `i` on `Z`,
which is `AlgebraicGeometry.Space.universalThickeningCompMap_restrict`.

This is the lower square of the composition law of part (3) of Stacks 04G2 for the conormal
sequence of the composition, and the square at which the left-hand arrow is formed. -/
public theorem universalThickeningComp_subspace_square :
    subspaceInclusion B S hS Z'
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩ ≫
        universalThickeningCompMap B S hS i hZ hY hfac =
      (ObjectProperty.homMk i :
          (⟨Z.toFunctor, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.1⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨Y.toFunctor, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1.1⟩) ≫
        subspaceInclusion B S hS Y'
          ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩ :=
  ObjectProperty.hom_ext _ (universalThickeningCompMap_restrict B S hS i hZ hY hfac)

/-- The conormal map of Stacks 060A at the square of
`AlgebraicGeometry.Space.universalThickeningComp_square`, read on `Z` itself: the map of
Stacks 04CP at `AlgebraicGeometry.Space.universalThickeningComp_subspace_square`.

This is what `AlgebraicGeometry.Space.universalThickeningConormalMap` at that square *is* by
definition — the canonical morphism of Stacks 060A for the square with `g = 𝟙 X` being
`AlgebraicGeometry.Space.universalThickeningCompMap`.  The left-hand arrow of the sequence is
its inverse image along the projection of the copy of `Z` inside the fibre product; writing it
at this spelling is what makes the composition law of part (3) of Stacks 04G2 apply, see the
implementation notes of this file. -/
public noncomputable def universalThickeningCompConormalLowerMap :=
  conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    (universalThickeningCompMap B S hS i hZ hY hfac) (ObjectProperty.homMk i)
    (universalThickeningComp_subspace_square B S hS i hZ hY hfac)

/-! ### The composite of the two arrows vanishes -/

/-- The conormal map of the lower square read as the map of Stacks 04CP at that square, which it
is by definition. -/
public theorem universalThickeningCompConormalLowerMap_eq :
    universalThickeningCompConormalLowerMap B S hS i hZ hY hfac =
      conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        (universalThickeningCompMap B S hS i hZ hY hfac) (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac) :=
  rfl

/-- The outer rectangle of the composition law of part (3) of Stacks 04G2 for the conormal
sequence of the composition: the inclusion of the copy of `Z` inside the fibre product
`Y ×_{Y'} Z'` followed by the composite `Z' ⟶ Y'` of clause (1) of Stacks 06BF is the projection
of that copy onto `Z` followed by the inclusion of the closed subspace `Y ⊆ Y'`. -/
private theorem universalThickeningComp_outer_rectangle :
    subspaceInclusion B S hS
          (universalThickeningCompFibre B S hS i hZ hY hfac)
          (preimageSubspace B S hS
            (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
            ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩) ≫
        universalThickeningCompFibreInclusion B S hS i hZ hY hfac ≫
          universalThickeningCompMap B S hS i hZ hY hfac =
      (preimageProjection B S hS
            (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
            ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩ ≫
          (ObjectProperty.homMk i :
            (⟨Z.toFunctor, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨Y.toFunctor,
              (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1.1⟩)) ≫
        subspaceInclusion B S hS Y'
          ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩ := by
  rw [← Category.assoc,
    conormalEtaleRestrictionSquare B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩,
    Category.assoc, universalThickeningComp_subspace_square B S hS i hZ hY hfac,
    Category.assoc]

/-- **The composite of the two arrows of the conormal sequence of the composition vanishes.**
By the composition law of part (3) of Stacks 04G2,
`AlgebraicGeometry.Space.conormalMap_comp`, the composite is the map of Stacks 04CP attached to
the outer rectangle, read through the composition comparison of Stacks 03LU, which is an
isomorphism.  The lower edge of that rectangle is the inclusion of the fibre product
`Y ×_{Y'} Z'` into `Z'` followed by the morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF, and
that composite factors through the closed subspace `Y ⊆ Y'` by the structure morphism
`AlgebraicGeometry.Space.universalThickeningCompStructure` of the fibre product — which is what
makes the fibre product a fibre product.  So the map of the outer rectangle vanishes by
`AlgebraicGeometry.Space.conormalMap_eq_zero_of_factorization`. -/
@[stacks 06BF "clause (2): the composite of the two maps of the sequence vanishes"]
public theorem universalThickeningCompConormalSequence_comp_eq_zero :
    modulePullbackMap B S hS
          (preimageProjection B S hS
            (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
            ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
          (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac) ≫
      universalThickeningCompConormalRightMap B S hS i hZ hY hfac = 0 := by
  have houter := universalThickeningComp_outer_rectangle B S hS i hZ hY hfac
  have hcomp := conormalMap_comp B S hS
    (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
    (universalThickeningCompMap B S hS i hZ hY hfac)
    (preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    (preimageProjection B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    (ObjectProperty.homMk i)
    (conormalEtaleRestrictionSquare B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    (universalThickeningComp_subspace_square B S hS i hZ hY hfac) houter
  have hvanish := conormalMap_eq_zero_of_factorization B S hS
    (preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    (universalThickeningCompFibreInclusion B S hS i hZ hY hfac ≫
      universalThickeningCompMap B S hS i hZ hY hfac)
    (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩ ≫
      ObjectProperty.homMk i)
    houter (universalThickeningCompStructure B S hS i hZ hY hfac)
    (ObjectProperty.hom_ext _
      (Subfunctor.fromPreimage_ι Y (universalThickeningCompMap B S hS i hZ hY hfac).hom))
  have h2 := hcomp.symm.trans hvanish
  have h3 := (Preadditive.IsIso.comp_left_eq_zero _ _).mp h2
  rw [← universalThickeningCompConormalLowerMap_eq B S hS i hZ hY hfac,
    ← universalThickeningCompConormalRightMap_eq B S hS i hZ hY hfac,
    ← modulePullbackMap_eq B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)] at h3
  exact h3

/-! ### Injectivity of the left-hand arrow is étale local -/

/-- **The injectivity clause descends from an étale chart.**  Injectivity of the left-hand arrow
of the conormal sequence of the composition after inverse image along one étale scheme chart
surjective on points gives it on the algebraic space, by
`mono_modulePullback_schemeChart_iff`. -/
public theorem mono_pullback_universalThickeningCompConormalLowerMap_of_chart
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hm : Mono ((modulePullback B S hS (ObjectProperty.homMk a :
        schemeSpace U ⟶ universalThickeningCompConormalBase B S hS i hZ hY hfac)).map
      (modulePullbackMap B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)))) :
    Mono (modulePullbackMap B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)) :=
  (mono_modulePullback_schemeChart_iff B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (modulePullbackMap B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)) U a haEtale haSurj).mp hm

/-! ### Exactness at the middle term -/

/-- **Exactness at `𝒞_{Z/X}` of the conormal sequence of the composition** — the middle clause of
Stacks 06BD in this presentation.  `AlgebraicGeometry.Space.exact_conormalShortComplex_preimage`
is that clause for a closed subspace inside the inverse image of a closed subspace downstairs,
which is what the fibre product `Y ×_{Y'} Z'` presents; its four comparison arguments are
discharged by the structural equations above, each of them an equation of single arrows.

With `AlgebraicGeometry.Space.universalThickeningCompConormalSequence_comp_eq_zero` above, which
supplies the vanishing the short complex is formed from, this is the middle-exactness assertion
of clause (2) of Stacks 06BF; the companion clauses of that tag are registered in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean`. -/
@[stacks 06BF "clause (2): exactness at the middle term"]
public theorem exact_universalThickeningCompConormalSequence :
    (ShortComplex.mk _ _
      (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac)).Exact :=
  exact_conormalShortComplex_preimage B S hS (universalThickeningCompMap B S hS i hZ hY hfac)
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    (ObjectProperty.homMk i)
    (universalThickeningComp_subspace_square B S hS i hZ hY hfac)
    (universalThickeningCompFibreSubspace B S hS i hZ hY hfac) rfl
    (universalThickeningCompFibreInclusion B S hS i hZ hY hfac) rfl
    (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)
    (universalThickeningCompConormalLowerMap_eq B S hS i hZ hY hfac)
    (modulePullbackMap B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac))
    (modulePullbackMap_eq B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac))
    (universalThickeningCompConormalRightMap B S hS i hZ hY hfac)
    (universalThickeningCompConormalRightMap_eq B S hS i hZ hY hfac)
    (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac)

/-! ### Short exactness -/

/-- The conormal sequence of the composition is short exact exactly when its left-hand arrow is
injective, unconditionally: the vanishing of the composite is
`AlgebraicGeometry.Space.universalThickeningCompConormalSequence_comp_eq_zero`, the exactness at
`𝒞_{Z/X}` is `AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence` and the
epimorphism at the right term is clause (2) of Stacks 06BF,
`AlgebraicGeometry.Space.epi_conormalMap_comp`. -/
public theorem shortExact_iff_mono_pullback_universalThickeningCompConormalLowerMap :
    (ShortComplex.mk _ _
        (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac)).ShortExact ↔
      Mono (modulePullbackMap B S hS
      (preimageProjection B S hS
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
      (universalThickeningCompConormalLowerMap B S hS i hZ hY hfac)) := by
  have hepi : Epi (universalThickeningCompConormalRightMap B S hS i hZ hY hfac) :=
    epi_conormalMap_comp B S hS i hZ hY hfac
  exact ⟨fun h => h.mono_f, fun h => ShortComplex.ShortExact.mk'
    (exact_universalThickeningCompConormalSequence B S hS i hZ hY hfac) h hepi⟩

end Chain

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocusSpreadOut

/-!
# Base change of the fibrewise associated-point locus

Let `f : X ⟶ Y` be a morphism of schemes, let `F` be an `𝒪_X`-module and let `U ⊆ X` be an
open subscheme, and write

`E(f, F, U) = {y : Y | Ass(F_y) ⊆ U_y}`

for the locus on the base over which all associated points of the fibre of `F` lie in `U`.
This file proves that `E` is compatible with base change along a morphism `g : Y' ⟶ Y` that
is surjective on stalks:

`E(f', F', U') = g ⁻¹' E(f, F, U)`,

where `f'` is the base change of `f`, `F'` the pullback of `F` and `U'` the inverse image of
`U` along the projection. This is part of the second obligation recorded in
`StacksFrontier/AlgebraicGeometry/Morphisms/ConstructibleAssociatedPointsLocusSpreadOut.lean`,
namely that "the fibrewise containment locus is the preimage of the corresponding locus under
any base change".

The hypothesis is `SurjectiveOnStalks g` rather than nothing at all, because that is what makes
the fibres literally comparable: `g` surjective on stalks makes `κ(g z) ⟶ κ(z)` an isomorphism,
so the fibre of `f'` at `z` is isomorphic to the fibre of `f` at `g z`. For a general `g` the
fibre of `f'` is the fibre of `f` base changed along a nontrivial extension of residue fields,
and the corresponding statement — Stacks 05KQ in full — needs the behaviour of associated
points under an extension of the base field, which is not proved here.

The restriction is therefore a genuine one, and it matters which of the two uses the source
makes of Stacks 05KQ it covers. It covers the spreading-out use: there 05KQ is applied to the
base change of `(f, F, U)` along an irreducible closed subset of the base given its reduced
induced structure, and a closed immersion is surjective on stalks. It does not cover the limit
use: there 05KQ is applied along `Spec A ⟶ Spec A_i` for a finite-type `ℤ`-subalgebra
`A_i ⊆ A`, whose stalk maps are localizations and are not surjective. A morphism inside the
source's class of 05KQ that is excluded here is `Spec ℚ(i) ⟶ Spec ℚ`.

## Main results

* `Stacks.Divisors.associatedPoints_congr`: isomorphic sheaves of modules have the same
  associated points.
* `Stacks.Divisors.associatedPoints_pullback_comp`: the associated points of a pullback along a
  composite are those of the iterated pullback.
* `Stacks.Divisors.associatedPoints_fiber_baseChange`: the associated points of the restriction
  of `F'` to the fibre of `f'` at `z` are the inverse image of the associated points of the
  restriction of `F` to the fibre of `f` at `g z`.
* `Stacks.Divisors.associatedPoints_fiber_subset_iff_baseChange`: **Stacks 05KQ** for a base
  change that is surjective on stalks — the fibrewise containment condition at `z` is the
  condition at `g z`.
* `Stacks.Divisors.setOf_associatedPoints_fiber_subset_baseChange`: the locus of the base change
  is the inverse image of the locus.
* `Stacks.Divisors.isLocallyConstructible_setOf_associatedPoints_fiber_subset_iff_of_isOpenCover`:
  the locus is locally constructible if and only if the locus of its base change to each member
  of an open cover of the base is. This is the change of base with which the proof of Stacks
  05KR opens; being an equivalence, it is no progress on constructibility itself.

## Implementation notes

The comparison morphism on fibres and the two facts about it that are used — that it is an
isomorphism when `g` induces an isomorphism of residue fields, which a morphism surjective on
stalks does, and that it matches the two inverse images of `U` — are the existing
`AlgebraicGeometry.baseChangeFiberMap`, `AlgebraicGeometry.isIso_baseChangeFiberMap` and
`AlgebraicGeometry.preimage_baseChangeFiberMap_eq`. What is added here is the module side.

The module side avoids computing with stalks: an isomorphism of sheaves of modules is a
monomorphism both ways, so Stacks 05AE
(`AlgebraicGeometry.associatedPoints_subset_of_mono`) gives both inclusions at once, and
`Mathlib`'s pseudofunctoriality isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp`
supplies the isomorphism. Composing the two pullbacks in the other order is then a rewrite
along an equality of scheme morphisms, which stays inside a proof of a set equality and so
introduces no transport in a data position.

No hypothesis of finite presentation on `f` or on `F` appears: every statement below holds for
an arbitrary morphism and an arbitrary sheaf of modules, and is therefore available under the
hypotheses of Stacks 05KR in particular.

## References

* [Stacks Project, Tag 05AE](https://stacks.math.columbia.edu/tag/05AE)
* [Stacks Project, Tag 05KQ](https://stacks.math.columbia.edu/tag/05KQ)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open scoped Set.Notation

universe u

namespace Stacks.Divisors

/-! ### Associated points of a pullback of modules -/

section Pullback

variable {X Y Z : Scheme.{u}}

/-- Isomorphic sheaves of modules have the same associated points: an isomorphism is a
monomorphism in both directions, so Stacks 05AE applies twice. -/
theorem associatedPoints_congr {F G : X.Modules} (e : F ≅ G) :
    associatedPoints F = associatedPoints G :=
  Set.Subset.antisymm (associatedPoints_subset_of_mono e.hom)
    (associatedPoints_subset_of_mono e.inv)

/-- The associated points of the pullback of a module along a composite `a ≫ b` are those of
the pullback along `b` followed by the pullback along `a`. -/
theorem associatedPoints_pullback_comp (a : X ⟶ Y) (b : Y ⟶ Z) (F : Z.Modules) :
    associatedPoints ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F)) =
      associatedPoints ((Scheme.Modules.pullback (a ≫ b)).obj F) :=
  associatedPoints_congr ((Scheme.Modules.pullbackComp a b).app F)

end Pullback

/-! ### Base change -/

section BaseChange

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (F : X.Modules) (U : X.Opens) (z : Y')

/-- An isomorphism of schemes is surjective on points. -/
private theorem surjective_of_isIso {W W' : Scheme.{u}} (e : W ⟶ W') [IsIso e] :
    Function.Surjective e := fun w =>
  ⟨inv e w, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; simp⟩

/-- The associated points of the restriction of the pullback of `F` to the fibre at `z` of the
base change of `f` along `g` are the inverse image, under the comparison morphism of fibres, of
the associated points of the restriction of `F` to the fibre of `f` at `g z`.

Both restrictions are pullbacks of `F` along the two legs of the commutative square
`baseChangeFiberMap_comp_fiberι`, so the two modules agree up to the pullback comparison
isomorphism; the comparison morphism of fibres is an isomorphism because `g` is surjective on
stalks. -/
theorem associatedPoints_fiber_baseChange [SurjectiveOnStalks g] :
    associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) =
      baseChangeFiberMap f g z ⁻¹'
        associatedPoints ((Scheme.Modules.pullback (f.fiberι (g z))).obj F) := by
  rw [associatedPoints_pullback_comp, ← baseChangeFiberMap_comp_fiberι,
    ← associatedPoints_pullback_comp]
  exact associatedPoints_pullback_of_iso (asIso (baseChangeFiberMap f g z)) _

/-- **Stacks Project, Tag 05KQ, for a base change that is surjective on stalks.** For
`g : Y' ⟶ Y` surjective on stalks, all associated points of the fibre at `z` of the pullback of
`F` lie in the inverse image of `U` exactly when all associated points of the fibre of `F` at
`g z` lie in `U`.

Both sides are read through the comparison morphism of fibres, which is an isomorphism and in
particular surjective, so the inverse image reflects containment. -/
theorem associatedPoints_fiber_subset_iff_baseChange [SurjectiveOnStalks g] :
    associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ⊆
        (pullback.snd f g).fiberι z ⁻¹' ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) :
          Set ↥(pullback f g)) ↔
      associatedPoints ((Scheme.Modules.pullback (f.fiberι (g z))).obj F) ⊆
        f.fiberι (g z) ⁻¹' (U : Set X) := by
  rw [associatedPoints_fiber_baseChange f g F z,
    show ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) : Set ↥(pullback f g)) =
      pullback.fst f g ⁻¹' (U : Set X) from rfl,
    preimage_baseChangeFiberMap_eq f g z U]
  exact (surjective_of_isIso (baseChangeFiberMap f g z)).preimage_subset_preimage_iff

/-- The fibrewise containment locus of the base change of `(f, F, U)` along a morphism `g` that
is surjective on stalks is the inverse image under `g` of the fibrewise containment locus of
`(f, F, U)`. -/
theorem setOf_associatedPoints_fiber_subset_baseChange [SurjectiveOnStalks g] :
    {z : Y' | associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ⊆
        (pullback.snd f g).fiberι z ⁻¹' ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) :
          Set ↥(pullback f g))} =
      g ⁻¹' {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)} :=
  Set.ext fun z => associatedPoints_fiber_subset_iff_baseChange f g F U z

end BaseChange

/-! ### Passage to an open cover of the base -/

/-- **Stacks Project, Tag 05KR is local on the base, as an equivalence.** The fibrewise
containment locus of `(f, F, U)` is locally constructible exactly when the fibrewise containment
locus of its base change to each member of an open cover of the base is.

This is deliberately an `Iff` and not an implication, so that its logical content is not
overstated: local constructibility is by definition a local condition, so the two sides are
equivalent and nothing is gained about constructibility here. What the statement does supply is
the change of base itself -- the right-hand side speaks about the base changes to the members of
the cover, which for a cover by affine opens is the situation the limit argument of the source
needs. The inclusion of an open subscheme is an open immersion, hence surjective on stalks, so
`setOf_associatedPoints_fiber_subset_baseChange` identifies the locus of each base change with
the restriction of the locus to that open. -/
theorem isLocallyConstructible_setOf_associatedPoints_fiber_subset_iff_of_isOpenCover
    {ι : Type*} {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (U : X.Opens)
    (V : ι → Y.Opens) (hV : IsOpenCover V) :
    IsLocallyConstructible
      {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)} ↔
      ∀ i, IsLocallyConstructible
        {z : (V i).toScheme | associatedPoints
            ((Scheme.Modules.pullback ((pullback.snd f (V i).ι).fiberι z)).obj
              ((Scheme.Modules.pullback (pullback.fst f (V i).ι)).obj F)) ⊆
          (pullback.snd f (V i).ι).fiberι z ⁻¹'
            ((pullback.fst f (V i).ι ⁻¹ᵁ U : (pullback f (V i).ι).Opens) :
              Set ↥(pullback f (V i).ι))} := by
  rw [IsLocallyConstructible.iff_of_isOpenCover hV]
  exact forall_congr' fun i => by
    rw [setOf_associatedPoints_fiber_subset_baseChange f (V i).ι F U]
    exact Iff.rfl

end Stacks.Divisors

end

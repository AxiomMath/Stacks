module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# The site-theoretic data behind a refinement of a groupoid scheme

Step 3 of the proof of [Stacks Project, Tag 0489] produces the coproduct `∐_u U'_u` of the
affine slices of [Stacks Project, Tag 04N0] over the finite type points of the object scheme,
and the source's footnote observes that this coproduct, and the source of its reach map, are
objects of the chosen big fppf site.  This module is the set-theoretic footnote and the
covering clause that go with it.

The three size estimates it needs are the library's: the source of *any* monomorphism into a
scheme of size below a strong prelimit again has size below it
(`AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit`), a fibre product of two such
schemes does (`AlgebraicGeometry.Scheme.size_pullback_lt`), and a coproduct is bounded by the
index set together with the summands (`AlgebraicGeometry.schemeSize_coproduct_le`).  The
coproduct estimate of [Stacks Project, Tag 000R] part (2),
`AlgebraicGeometry.Scheme.size_sigmaObj_lt`, is *not* usable: it needs the index type to be at
most countable, because only the uncountable cofinality of the cutoff bounds the supremum of
the summands' sizes.  Here the summands have a bound independent of the index -- all of them are
sources of monomorphisms into one scheme -- so the supremum is harmless and the index type may
be as large as the set of points of that scheme.

## Main results

* `AlgebraicGeometry.mono_left_of_mono_over`: a monomorphism of `Over B` has monic underlying
  morphism.
* `AlgebraicGeometry.Scheme.size_sigma_lt_of_mono`: the coproduct of a family of sources of
  monomorphisms into one scheme `Y`, indexed by at most the points of `Y`, has size below any
  strong prelimit above the size of `Y`.
* `AlgebraicGeometry.BigFppfSite.contains_arrows_of_isEquivalenceRelation`: the arrow scheme of
  an equivalence-relation groupoid whose object scheme belongs to a big fppf site belongs to it
  too, since `(t, s) : R ⟶ U ×_S U` is a monomorphism.
* `AlgebraicGeometry.Space.singleton_mem_bigFppfOver_topology_of_flat`: a surjective, flat,
  locally finitely presented morphism of the big fppf site *over `S`* generates a covering
  sieve.  This is `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology_of_flat` transported
  along the localization of the topology at `S`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-! ### Monomorphisms of a slice category -/

/-- A monomorphism of `Over B` is a monomorphism on underlying objects.

A morphism `a : Z ⟶ X.left` equalized after composition with `f.left` is a morphism of
`Over B` out of `Over.mk (a ≫ X.hom)`, and `f` cancels there. -/
theorem mono_left_of_mono_over {C : Type*} [Category C] {B : C} {X Y : Over B} (f : X ⟶ Y)
    [Mono f] : Mono f.left := by
  constructor
  intro Z a b hab
  have hw : b ≫ X.hom = a ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hab]
  have h : (Over.homMk a : Over.mk (a ≫ X.hom) ⟶ X) = Over.homMk b hw :=
    (cancel_mono f).mp (Over.OverMorphism.ext hab)
  exact congrArg Over.Hom.left h

/-! ### The coproduct of the sources of monomorphisms into a fixed scheme -/

/-- **The coproduct estimate of the footnote to Step 3 of the proof of
[Stacks Project, Tag 0489].**

Let `g i : V i ⟶ Y` be a family of monomorphisms of schemes indexed by a type no larger than
the set of points of `Y`, and let `κ` be a cardinal closed under powersets with
`size Y < κ`.  Then `size (∐ V) < κ`.

`AlgebraicGeometry.Scheme.size_le_of_mono` bounds every summand by
`max (2 ^ #Y) (size Y)` -- a bound independent of the index -- and that same cardinal bounds
the index type, since `#I ≤ #Y ≤ 2 ^ #Y`.  So the open-cover estimate
`AlgebraicGeometry.schemeSize_coproduct_le` applies at that cardinal, which lies below `κ` by
`AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit`. -/
theorem Scheme.size_sigma_lt_of_mono {κ : Cardinal.{u}} (hsl : Cardinal.IsStrongPrelimit κ)
    {Y : Scheme.{u}} (hY : Y.size < κ) {I : Type u} (V : I → Scheme.{u})
    (g : ∀ i, V i ⟶ Y) (hg : ∀ i, Mono (g i)) (hI : #I ≤ #(Y : Type u)) :
    (∐ V).size < κ := by
  refine (schemeSize_coproduct_le V (max (2 ^ #(Y : Type u)) Y.size)
    (le_max_of_le_right (Scheme.aleph0_le_size Y))
    (le_max_of_le_left (hI.trans (Cardinal.cantor _).le)) fun j => ?_).trans_lt
    (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit hsl hY)
  have := hg j
  exact Scheme.size_le_of_mono (g j)

/-! ### The arrow scheme of an equivalence relation -/

/-- **The arrow scheme of an equivalence-relation groupoid belongs to the site.**

For an internal equivalence relation the pre-relation `(t, s) : R ⟶ U ×_S U` is a
monomorphism, so `R` is the source of a monomorphism into `U ×_S U`, whose size is below the
cutoff because `U` is and the cutoff is closed under fibre products.  The cutoff being a strong
prelimit, `AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit` needs nothing of the
monomorphism itself.

This is what makes the source of the reach map of Step 3 of the proof of
[Stacks Project, Tag 0489] an object of the site: that source is `U' ×_{g, U, t} R`. -/
theorem BigFppfSite.contains_arrows_of_isEquivalenceRelation (B : BigFppfSite.{u})
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    (hU : B.Contains G.objects.left) : B.Contains G.arrows.left := by
  have hrel : CategoryTheory.IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source := by
    rw [show (groupoidPreRelation G).target = G.target from prod.lift_fst _ _,
      show (groupoidPreRelation G).source = G.source from prod.lift_snd _ _]
    infer_instance
  have _ : Mono (groupoidPreRelation G) :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
      (groupoidPreRelation G)).mp hrel).1
  have _ : Mono (groupoidPreRelation G).left := mono_left_of_mono_over _
  refine Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
    (groupoidPreRelation G).left ?_
  rw [Scheme.size_congr (Over.prodLeftIsoPullback G.objects G.objects)]
  exact Scheme.size_pullback_lt _ _ hU hU

/-! ### A flat singleton covering of the big fppf site over `S` -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site over `S` which is surjective, flat and locally of finite
presentation as a morphism of schemes generates a covering sieve.

This is `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology_of_flat` read through the
localization `BigFppfOver.topology B S hS = B.topology.over (B.obj hS)`: a sieve of the slice
covers exactly when its image sieve does. -/
theorem singleton_mem_bigFppfOver_topology_of_flat {X Y : BigFppfOver B S hS} (a : X ⟶ Y)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map a))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map a))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map a)) :
    Sieve.generate (Presieve.singleton a) ∈ BigFppfOver.topology B S hS Y := by
  show Sieve.generate (Presieve.singleton a) ∈ B.topology.over (B.obj hS) Y
  rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
    Presieve.map_singleton]
  exact singleton_mem_bigFppf_topology_of_flat B a.left hsurj hflat hlfp

end Space

end AlgebraicGeometry

end

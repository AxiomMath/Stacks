module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact

/-!
# The comparison out of an exterior algebra is an isomorphism as soon as it is so locally

Let `R` be a sheaf of rings on a site `(C, J)`, let `M` be a sheaf of `R`-modules, let `A` with a
degree-one generator `ι` be the exterior algebra of `M`
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra`) and let `B` be any sheaf of graded
`R`-algebras with a square-zero degree-one generator `κ`. The universal property produces the
comparison homomorphism `A ⟶ B` extending `κ`, and the question whether its degree-`n` component

`A^n ⟶ B^n`

is an isomorphism is **local on the site**: it suffices that it be one after restriction to the
members of a family `{V i}` covering the final object.

This is the formal content of the sentence "to see this is true we may work locally" with which
the proof of [Stacks, Tag 0BQY] opens, read on the comparison map rather than on the geometry:
the degreewise comparison of that tag is a `desc` out of an exterior algebra, and the tag's
proof establishes its invertibility only on the members of a cover.

## Main definitions

* `SheafOfModules.GradedAlgebra.UnitalHom.over`: restriction of a homomorphism of sheaves of
  graded algebras to the slice site at an object, along
  `SheafOfModules.GradedAlgebra.over`.

## Main results

* `SheafOfModules.GradedAlgebra.SquareZero.over`: a square-zero degree-one generator restricts
  to a square-zero degree-one generator, and
  `SheafOfModules.GradedAlgebra.SquareZero.of_coversTop`: **the square-zero condition is local
  on the site** — it holds as soon as it holds after restriction to the members of a covering
  family. This is the only hypothesis the comparison map out of an exterior algebra needs, so a
  globally defined comparison may be built from local square-zero statements alone.
* `SheafOfModules.GradedAlgebra.UnitalHom.isIso_app_of_coversTop`: **the gluing primitive** — a
  homomorphism of sheaves of graded algebras whose degree-`n` component becomes an isomorphism
  after restriction to the members of a covering family has that component an isomorphism.
* `SheafOfModules.GradedAlgebra.IsUniversal.desc_over` and
  `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.desc_over`: **the comparison homomorphism
  commutes with restriction** — the restriction of `desc` is the `desc` of the restrictions,
  whenever the restricted algebra is again universal.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`: **the
  local-to-global step.** If the restrictions of `A` and of `B` to the members of a covering
  family are again exterior algebras on the restricted generators, then every degree-`n`
  component of the comparison `A ⟶ B` is an isomorphism.
* `SheafOfModules.GradedAlgebra.UnitalHom.ext_of_coversTop`: two homomorphisms of sheaves of
  graded algebras agreeing after restriction to the members of a covering family are equal.

## Implementation notes

**Restriction of the algebra data is free, and that is why `desc_over` is provable at all.**
`SheafOfModules.GradedAlgebra.over` leaves the underlying presheaves untouched: every field of
the restricted algebra is the corresponding field of the original evaluated at `op V.unop.left`
(`SheafOfModules.GradedAlgebra.over_mul_app` and its companions are `rfl`). So the restriction
of a unital homomorphism is again one with no transport, and the identity
`ι|_U ≫ (desc)|_U = κ|_U` to be fed to the uniqueness clause is the image of
`ι ≫ desc = κ` under a functor.

**What the two local hypotheses are, and why both are needed.** `desc` is extracted from an
`ExistsUnique` and is therefore not computed by anything; the only handle on it is uniqueness.
To recognise the restricted `desc` as the `desc` of the restrictions one needs the *source* to
be universal over the slice site (`hAV`), and to recognise that `desc` as an isomorphism one
needs the *target* to be universal there too (`hBV`), at which point
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso` applies. Neither follows from the global
universal property: a graded algebra over the slice site need not be the restriction of one on
`C`, so the global property says nothing about the test objects the local property quantifies
over.

**Only joint conservativity is used, not descent.** The conclusion is the invertibility of a
morphism that already exists globally, so
`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map` suffices and no gluing of locally defined
morphisms is required. The companion statement that the *universal property itself* is local —
that `A` is an exterior algebra as soon as each `A|_{V i}` is — would need such gluing, and only
its uniqueness half is available here, as `UnitalHom.ext_of_coversTop`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R}

/-- **The restriction of a degree-one generator to the slice site at `U`.** The target is
`(A.over U).piece 1`, which is `(A.piece 1).over U` definitionally. -/
abbrev genOver (ι : M ⟶ A.piece 1) (U : C) : M.over U ⟶ (A.over U).piece 1 :=
  _root_.SheafOfModules.Hom.over ι U

/-- **The restriction of a homomorphism of sheaves of graded algebras to the slice site at
`U`.** Each component is the restriction of the corresponding component, and the two
compatibilities are the original ones read at the objects of the slice site, the restricted
algebra having the same multiplication and the same unit there. -/
def UnitalHom.over (g : UnitalHom A B) (U : C) : UnitalHom (A.over U) (B.over U) where
  app n := _root_.SheafOfModules.Hom.over (g.app n) U
  map_mul i j V x y := g.map_mul i j (op V.unop.left) x y
  map_one V := g.map_one (op V.unop.left)

/-- The degree-`n` component of the restriction of `g` to the slice site at `U` is the
restriction of the degree-`n` component of `g`. -/
@[simp] theorem UnitalHom.over_app (g : UnitalHom A B) (U : C) (n : ℤ) :
    (g.over U).app n = _root_.SheafOfModules.Hom.over (g.app n) U := rfl

/-- **A square-zero degree-one generator restricts to a square-zero degree-one generator.** The
restricted algebra's multiplication on the sections over an object of the slice site is the
original multiplication on the sections over its underlying object. -/
theorem SquareZero.over {ι : M ⟶ A.piece 1} (h : SquareZero ι) (U : C) :
    SquareZero (A := A.over U) (genOver ι U) :=
  fun V s => h (op V.unop.left) s

/-- **The square-zero condition on a degree-one generator is local on the site.** If the
restriction of `ι` to the slice site at `V i` has square zero for a family `{V i}` covering the
final object, then `ι` has square zero.

The square of a local section is a section of the degree-two piece, which is a sheaf, hence
separated; and every object of the site is covered by objects admitting a morphism to some
`V i`, over which the restriction of that square is the square computed in the restricted
algebra. -/
theorem SquareZero.of_coversTop {ι : M ⟶ A.piece 1} {I : Type*} {V : I → C}
    (hV : J.CoversTop V)
    (h : ∀ i, SquareZero (A := A.over (V i)) (genOver ι (V i))) : SquareZero ι := by
  intro U s
  refine (A.piece (1 + 1)).isSheaf.isSeparated _ _ (hV.cover U.unop).2 _ _ ?_
  rintro W f ⟨i, ⟨b⟩⟩
  refine Eq.trans ((A.mul 1 1).naturality f.op _ _) (Eq.trans ?_ (map_zero _).symm)
  exact Eq.trans
    (congrArg (fun z => (A.mul 1 1).app (op W) z z)
      (PresheafOfModules.naturality_apply ι.val f.op s).symm)
    (h i (op (Over.mk b)) (M.val.map f.op s))

variable {P : ∀ D : GradedAlgebra.{t, a} R, (M ⟶ D.piece 1) → Prop}

/-- **The comparison homomorphism out of a universal graded algebra commutes with restriction to
a slice site.** If the restriction of `A` to the slice site at `U` is again universal for the
local property `P'`, and the restricted generator of `B` has `P'`, then the restriction of the
homomorphism `A ⟶ B` extending `κ` is the homomorphism `A|_U ⟶ B|_U` extending `κ|_U`.

Both sides extend `κ|_U`: the left-hand one because extending is a composition, which the
restriction functor preserves, and the right-hand one by construction. Uniqueness in the local
universal property identifies them. -/
theorem IsUniversal.desc_over {ι : M ⟶ A.piece 1} (hA : IsUniversal P A ι)
    {U : C} {P' : ∀ D : GradedAlgebra.{t, a} (R.over U), (M.over U ⟶ D.piece 1) → Prop}
    (hAU : IsUniversal P' (A.over U) (genOver ι U))
    (κ : M ⟶ B.piece 1) (hκ : P B κ) (hκU : P' (B.over U) (genOver κ U)) :
    (hA.desc B κ hκ).over U = hAU.desc (B.over U) (genOver κ U) hκU :=
  hAU.desc_unique _ _ _ <| by
    have h := congrArg (fun f => (_root_.SheafOfModules.overFunctor.{a} R U).map f)
      (hA.desc_extends B κ hκ)
    simpa [UnitalHom.over, genOver] using h

/-- **The comparison homomorphism out of an exterior algebra commutes with restriction to a
slice site**, the `P = SquareZero` case of `IsUniversal.desc_over`. -/
theorem IsExteriorAlgebra.desc_over {ι : M ⟶ A.piece 1} (hA : IsExteriorAlgebra A ι) {U : C}
    (hAU : IsExteriorAlgebra (A.over U) (genOver ι U))
    (κ : M ⟶ B.piece 1) (hκ : SquareZero κ) :
    (hA.desc B κ hκ).over U = hAU.desc (B.over U) (genOver κ U) (hκ.over U) :=
  IsUniversal.desc_over hA hAU κ hκ (hκ.over U)

/-- **A homomorphism of sheaves of graded algebras which is an isomorphism in degree `n` after
restriction to the members of a covering family is one.** The gluing primitive: restriction to
the slices at a family of objects covering the final object is jointly conservative on sheaves
of modules, and the homomorphism in question already exists globally, so no descent of locally
defined morphisms is involved. -/
theorem UnitalHom.isIso_app_of_coversTop (g : UnitalHom A B) {I : Type*} {V : I → C}
    (hV : J.CoversTop V) (n : ℤ) (h : ∀ i, IsIso ((g.over (V i)).app n)) :
    IsIso (g.app n) :=
  Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hV _ h

/-- **The comparison out of an exterior algebra is an isomorphism in every degree as soon as it
is so locally.** Let `A` with `ι` be the exterior algebra of `M`, let `κ : M ⟶ B.piece 1` be a
square-zero degree-one generator and let `{V i}` be a family of objects covering the final
object. If, for every `i`, the restrictions of `A` and of `B` to the slice site at `V i` are
exterior algebras on the restricted generators, then every degree-`n` component of the
comparison homomorphism `A ⟶ B` extending `κ` is an isomorphism.

The restriction of the comparison to the slice at `V i` is the comparison between two exterior
algebras of `M|_{V i}` (`IsExteriorAlgebra.desc_over`), hence the isomorphism
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceIso`; and restriction to the members of a
covering family is jointly conservative on sheaves of modules
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`). -/
theorem IsExteriorAlgebra.isIso_desc_app_of_coversTop {ι : M ⟶ A.piece 1}
    (hA : IsExteriorAlgebra A ι) (κ : M ⟶ B.piece 1) (hκ : SquareZero κ)
    {I : Type*} {V : I → C} (hV : J.CoversTop V)
    (hAV : ∀ i, IsExteriorAlgebra (A.over (V i)) (genOver ι (V i)))
    (hBV : ∀ i, IsExteriorAlgebra (B.over (V i)) (genOver κ (V i))) (n : ℤ) :
    IsIso ((hA.desc B κ hκ).app n) :=
  UnitalHom.isIso_app_of_coversTop _ hV n fun i => by
    rw [hA.desc_over (hAV i) κ hκ]
    exact ((hAV i).pieceIso (hBV i) n).isIso_hom

end SheafOfModules.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{a}}
  {A B : GradedAlgebra.{a, a} R}

/-- **Two homomorphisms of sheaves of graded algebras which agree after restriction to the
members of a covering family are equal.** This is the uniqueness half of the statement that the
universal property of an exterior algebra is local: restriction to the members of a family
covering the final object is a jointly faithful family of functors on sheaves of modules
(`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`), and a homomorphism of
sheaves of graded algebras is determined by its components. -/
theorem UnitalHom.ext_of_coversTop {I : Type*} {V : I → C} (hV : J.CoversTop V)
    (g h : UnitalHom A B) (hgh : ∀ i, g.over (V i) = h.over (V i)) : g = h :=
  UnitalHom.ext fun n =>
    Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective hV _ _ fun i =>
      congrArg (fun k : UnitalHom (A.over (V i)) (B.over (V i)) => k.app n) (hgh i)

end SheafOfModules.GradedAlgebra

end

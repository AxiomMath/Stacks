module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize

/-!
# Change of base scheme (Stacks 04X5, Construction A)

Let `g : S ⟶ S'` be a morphism of a big fppf site. A category over the big fppf site of `S` is
also a category over the big fppf site of `S'`, by composing its structure functor with
`CategoryTheory.Over.map g`; this is Construction A of Stacks, Section 04WT for these two sites,
and it is what Stacks 04X6 calls viewing a stack over `S` as a stack over `S'`. The construction
loses no information, because the big fppf site of `S` *is* the localization of the big fppf site
of `S'` at its object `S/S'`: under `CategoryTheory.Over.iteratedSliceEquiv (Over.mk g)` the
functor `Over.map g` is the localization functor `Over.forget (Over.mk g)`
(`map_eq_forget_iteratedSlice`, Stacks 03EH), and the localized topology matches
(Mathlib's `IsDenseSubsite` instance for the iterated slice).

## Main definitions

* `AlgebraicGeometry.Stack.changeBase`: Construction A on the underlying based category.
* `AlgebraicGeometry.Stack.changeBaseFiberedInGroupoids`: Construction A on a category fibred in
  groupoids.
* `AlgebraicGeometry.Stack.changeBaseFunctor`: Construction A on a 1-morphism.
* `AlgebraicGeometry.Stack.changeBaseHom`: Construction A on a 1-morphism of the 2-category of
  categories fibred in groupoids.
* `AlgebraicGeometry.Stack.factorSliceFunctor` and
  `AlgebraicGeometry.Stack.factorSliceInverse`: the identification of the slice of the big fppf
  site of `S'` over an object whose structure morphism factors through `S` with the corresponding
  slice of the big fppf site of `S`.
* `AlgebraicGeometry.Stack.changeBaseAlgebraicStack`: Construction A on an object of the
  2-category of algebraic stacks of Stacks 03YP.

## Main results

* `CategoryTheory.Over.exists_eq_map_of_comp_forget` and
  `CategoryTheory.Over.exists_eq_map_of_comp_map`: a functor between slice categories that is
  strictly over the ambient category is postcomposition with a morphism; so one that becomes a
  relocalization after relocalizing is itself a relocalization, along a factorization.
* `AlgebraicGeometry.Stack.changeBase_p_eq_comp_forget_iteratedSlice`: the structure functor of
  `changeBase` is the localization functor of the big fppf site of `S'` at `S/S'`, read through
  the iterated-slice identification.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_changeBase_iff`: Construction A neither creates
  nor destroys the property of being fibred in groupoids, which is the first of the four clauses
  of Stacks 026O.
* `AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` and
  `AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`: the scheme-valued points of
  `changeBase 𝒳` over `S'` are exactly the scheme-valued points of `𝒳` over `S`. This is the
  source's remark that the statement of Stacks 04X5 makes sense because the functor between the
  two sites is a localization functor.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`:
  representability by algebraic spaces (Stacks 02ZW) is unchanged by Construction A, which is the
  second of the four clauses of Stacks 026O in the form in which that clause is used.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_comp_overMap_iff`: surjectivity on objects
  (Stacks 06D4) is unchanged by Construction A.
* `AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff`: the relative
  surjectivity of Stacks 03YK is unchanged by Construction A. This is the surjectivity half of
  the presentation clause of Stacks 026O.
* `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`: the relative property of
  Stacks 03YK at the every-étale-chart condition of Stacks 03MJ for an arbitrary property of
  scheme morphisms is unchanged by Construction A. At smoothness this is the smoothness half of
  that clause, so the presentation clause of Stacks 026O transfers in full.
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_changeBase_iff`: condition (3) of Stacks
  045G is unchanged by Construction A.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`:
  representability of the diagonal — the second of the four clauses of Stacks 026O — is unchanged
  by Construction A.
* `AlgebraicGeometry.Stack.eq_of_isCovering` and
  `AlgebraicGeometry.Stack.exists_factorization_of_isCovering`: a covering family of the big fppf
  site of `S'` is jointly epimorphic, and the structure morphism of its target factors through
  `g` as soon as those of its members do, compatibly. These are the two inputs the
  stack-in-groupoids clause of Stacks 026O needs of the fppf topology.
* `AlgebraicGeometry.Stack.isStackInGroupoids_of_changeBase` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_changeBase`: the two directions of the
  stack-in-groupoids clause of Stacks 026O for Construction A, packaged as
  `AlgebraicGeometry.Stack.isStackInGroupoids_changeBase_iff`. This is the family-indexed half of
  the third of the four clauses of Stacks 026O, in full.
* `AlgebraicGeometry.Stack.isStack_changeBase_iff`: the sieve-indexed half of that clause, i.e.
  the stack condition of Stacks 026F, is unchanged by Construction A.
* `AlgebraicGeometry.Stack.forall_isSurjective_and_isSmooth_iff_hasRelativeProperty`: the
  presentation clause of Stacks 026O is the conjunction of two instances of Stacks 03YK.
* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalence_source`: Stacks 03YK is
  unchanged by an equivalence of the source of the 1-morphism.
* `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`: **the algebraicity criterion of
  Stacks 04X5**, assembled from the four clauses. It is what makes
  `AlgebraicGeometry.Stack.changeBaseAlgebraicStack` well defined.

## Implementation notes

The underlying type and category of `changeBase` are those of the input on the nose, so the two
structure functors differ only by the composition, and every statement comparing them is about
`𝒳.p` versus `𝒳.p ⋙ Over.map g`. That is why the fibred-in-groupoids clause transfers by the
general `CategoryTheory.Functor.isFiberedInGroupoids_comp_overMap_iff` with no reference to the
fppf topology.

The universes of the total category are free, as in `CategoryTheory.BasedCategory`, for every
clause but the sieve-indexed stack condition; Stacks 04X5 is stated with the object universe one
above the scheme universe, which is this with `t := u + 1`. The sieve-indexed condition is
transferred only at that pinned universe, because Construction B of Stacks 04WV
(`CategoryTheory.Over.isStack_of_comp_forget`) relates two categories over the same site in the
same universes; `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` is accordingly stated
at `BasedCategory.{u, u + 1}`, which is where Stacks 04X5 states it.

The transfer of representability by algebraic spaces rests on two things, and on nothing about
the fppf topology. The first is the points correspondence above. The second is
`CategoryTheory.TwoFibreProductOver.fstEquivalenceOver`: relocalizing the base does not change the
2-fibre product of a scheme-valued point with a 1-morphism, as an equivalence over the big fppf
site of the point's scheme. So the representing algebraic space is literally the same object on
both sides of the biconditional, and no transport of algebraicity along a comparison is needed.

Relative surjectivity is transferred without any statement about the lower-shriek extension at
all. Stacks 06D7 (`AlgebraicGeometry.Stack.isSurjectiveOnObjects_iff_isRelativelySurjective`)
replaces it by surjectivity on objects, Stacks 06D4, and that condition mentions the structure
functor only through the objects of the site it hits and the morphisms of the site lifting a
given morphism of the total category. Both are unchanged by composing with
`CategoryTheory.Over.map g`: an object of the big fppf site of `S` has the same underlying scheme
when read over `S'`, so it is the spectrum of a field on one side exactly when it is on the
other; and a morphism of the site lifting a given morphism of the total category is pinned down
by that morphism, which is `CategoryTheory.Functor.isHomLift_comp_map` in one direction and the
canonical factorization through `pY.map α` in the other.

Relative smoothness, by contrast, really does need the lower-shriek extension of Stacks 03I5
part (2), since smoothness has no objects-level criterion. What it needs of it is that the
every-étale-chart condition of Stacks 03MJ for the structural morphism of the extension does not
depend on the base, which is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`; the
quantifications over scheme-valued points and over representing algebraic spaces match up exactly
as for representability, so the morphism being tested is the same on both sides.

The diagonal clause does not compare the two diagonals. The targets are *not* isomorphic:
`CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence` compares the self-product over the
big fppf site of `S` with the one whose comparison isomorphism still lives over that site, where
the self-product of `changeBase 𝒳` over the big fppf site of `S'` has a comparison isomorphism
over the larger site, and so has the strictly larger object set of pairs lying over a common
`S'`-scheme by two different morphisms to `S`. The clause is instead read through Stacks 045G: by
its conditions (1), (2) and (3) it is equivalent to `IsRepresentableFromSchemes`, and *that*
transfers, because a 1-morphism out of a scheme-valued point sees only one morphism to `S` at a
time — and because such a 1-morphism into `changeBase 𝒳` forces the structure morphism of its
source to factor through `S`, by the rigidity of relocalization
(`CategoryTheory.Over.exists_eq_map_of_comp_map`), so there is nothing to say about objects of the
site of `S'` that do not come from the site of `S`. The equalizer of the two morphisms to `S`,
which a direct comparison of the self-products would have to form, is absorbed into the
already-proved equivalence of conditions (2) and (3).

All four clauses of Stacks 026O are transferred here, and
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` assembles them: the first is
`isFiberedInGroupoids_changeBase_iff`, the second is
`isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`, the third is
`isStack_changeBase_iff` together with `isStackInGroupoids_changeBase_iff`, and the fourth is
`hasRelativeProperty_surjective_changeBaseHom_iff` together with
`hasRelativeProperty_smooth_changeBaseHom_iff`.

**Not here.** Stacks 04X5 also asks for an isomorphism of the 2-categories of *algebraic* stacks.
The algebraicity criterion is what makes its map on objects well defined, and that map is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` below; the bijections on objects, 1-morphisms
and 2-morphisms that bundle it into the correspondence are
`AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv`,
`AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv` and
`AlgebraicGeometry.Stack.algebraicStackConstructionHom₂Equiv`, which carry the part key of
Stacks 04X5 for the canonical 2-categorical correspondence and are proved in a separate module.

The stack-in-groupoids clause is the one whose transfer is *not* a formality, and the reason is
the same one that defeats a direct comparison of the two diagonals. The `Isom`-sheaf condition
and the effectivity condition of
`CategoryTheory.Functor.IsStackInGroupoids` are indexed by an object `U'` of the big fppf site of
`S'`, and they quantify over objects of the total category lying over `U'` for the composed
structure functor — which is to say over *any* object of the big fppf site of `S` with the same
underlying scheme whose structure morphism composed with `g` is that of `U'`. Two such objects
need not be equal. So the conditions over `S'` compare data lying over two different morphisms to
`S`, exactly as the self-product of `changeBase 𝒳` does, and the only thing that identifies the
two morphisms is that they agree on a covering family: the fppf topology of a big fppf site is
subcanonical (`AlgebraicGeometry.BigFppfSite.subcanonical_topology`), so a covering family is
jointly epimorphic and a compatible family of factorizations through `g` glues. Those two
consequences
are `AlgebraicGeometry.Stack.eq_of_isCovering` and
`AlgebraicGeometry.Stack.exists_factorization_of_isCovering`, proved here, and the change-of-slice
transfer of the remaining notions — `CategoryTheory.Functor.Restriction`,
`CategoryTheory.Functor.FibreHom`, `CategoryTheory.Functor.IsRestrictionOf` and the pullback
overlaps — is
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/StackOverMap.lean`.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v₁ u₁

variable {T : Type u₁} [Category.{v₁} T]

/-- **A functor between slice categories which is strictly over the ambient category is
postcomposition with a morphism.** The morphism is the structure morphism of the image of the
terminal object `V/V`, and the value of the functor at any `A` is recovered from it because the
unique morphism `A ⟶ V/V` is sent to a morphism of `T/W` whose underlying morphism of `T` is
again the structure morphism of `A`. -/
lemma exists_eq_map_of_comp_forget {V W : T} (F : Over V ⥤ Over W)
    (hF : F ⋙ Over.forget W = Over.forget V) :
    ∃ h : V ⟶ W, F = Over.map h := by
  have hleft : ∀ A : Over V, (F.obj A).left = A.left := fun A =>
    congrArg (fun G : Over V ⥤ T => G.obj A) hF
  have hmapleft : ∀ {A B : Over V} (φ : A ⟶ B), (F.map φ).left =
      eqToHom (hleft A) ≫ φ.left ≫ eqToHom (hleft B).symm := by
    intro A B φ
    simpa using Functor.congr_hom hF φ
  refine ⟨eqToHom (hleft (Over.mk (𝟙 V))).symm ≫ (F.obj (Over.mk (𝟙 V))).hom, ?_⟩
  have hobj : ∀ A : Over V, F.obj A =
      (Over.map (eqToHom (hleft (Over.mk (𝟙 V))).symm ≫
        (F.obj (Over.mk (𝟙 V))).hom)).obj A := by
    intro A
    refine CostructuredArrow.obj_ext _ _ (hleft A) ?_
    have hw := Over.w (F.map (Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 V)))
    rw [hmapleft] at hw
    simp only [Functor.id_obj, Functor.id_map, Over.map_obj_hom, Over.mk_left,
      Over.homMk_left] at hw ⊢
    simpa using hw
  refine Functor.ext hobj ?_
  intro A B φ
  apply Over.OverMorphism.ext
  rw [hmapleft]
  simp [Over.eqToHom_left]

/-- **Rigidity of relocalization.** A functor `T/V ⥤ T/W` which becomes postcomposition with
`c : V ⟶ W'` after postcomposing with `g : W ⟶ W'` is itself postcomposition with a factorization
of `c` through `g`.

This is what makes the statement of Stacks 04X5 meaningful: a scheme-valued point of a category
over the big fppf site of `S`, read over the big fppf site of `S'`, remembers the morphism to `S`
it came from. -/
lemma exists_eq_map_of_comp_map {V W W' : T} (g : W ⟶ W') (c : V ⟶ W')
    (F : Over V ⥤ Over W) (hF : F ⋙ Over.map g = Over.map c) :
    ∃ h : V ⟶ W, F = Over.map h ∧ h ≫ g = c := by
  have h1 : F ⋙ Over.forget W = Over.forget V := by
    rw [← Over.mapForget_eq g, ← Functor.assoc, hF, Over.mapForget_eq]
  obtain ⟨h, rfl⟩ := exists_eq_map_of_comp_forget F h1
  refine ⟨h, rfl, ?_⟩
  rw [← Over.mapComp_eq] at hF
  simpa using (Over.w (eqToHom (Functor.congr_obj hF (Over.mk (𝟙 V))))).symm

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u v t v₂ t₂ uX uY vX vY w vP

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Construction A of Stacks, Section 04WT for the big fppf sites of `S` and `S'`.** A category
over the big fppf site of `S` is viewed over the big fppf site of `S'` by composing its structure
functor with the relocalization functor `CategoryTheory.Over.map g` of `g : S ⟶ S'`. The original
structure functor is then the 1-morphism of the result to the category of schemes over `S`. -/
def changeBase (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    BasedCategory.{v, t} (BigFppfOver B S' hS') where
  obj := 𝒳.obj
  category := 𝒳.category
  p := 𝒳.p ⋙ Over.map g

/-- The underlying category of `changeBase 𝒳` is that of `𝒳`. -/
@[simp]
lemma changeBase_obj (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).obj = 𝒳.obj :=
  rfl

/-- The structure functor of `changeBase 𝒳` is that of `𝒳` composed with `Over.map g`. -/
@[simp]
lemma changeBase_p (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p = 𝒳.p ⋙ Over.map g :=
  rfl

/-- The structure functor produced by Construction A is the composite of the original one with the
localization functor of the big fppf site of `S'` at its object `S/S'`, read through the
iterated-slice identification of that localization with the big fppf site of `S`. This is the
remark that makes the statement of Stacks 04X5 meaningful. -/
lemma changeBase_p_eq_comp_forget_iteratedSlice
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p =
      𝒳.p ⋙ (Over.mk g).iteratedSliceBackward ⋙ Over.forget (Over.mk g) :=
  rfl

/-- **The first clause of Stacks 026O is unchanged by Construction A.** A category over the big
fppf site of `S` is fibred in groupoids exactly when the category over the big fppf site of `S'`
produced by Construction A is. -/
theorem isFiberedInGroupoids_changeBase_iff (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p.IsFiberedInGroupoids ↔ 𝒳.p.IsFiberedInGroupoids :=
  Functor.isFiberedInGroupoids_comp_overMap_iff g 𝒳.p

/-- Construction A on a category fibred in groupoids over the big fppf site of `S`, using
`AlgebraicGeometry.Stack.isFiberedInGroupoids_changeBase_iff` to see that the result is again
fibred in groupoids. -/
def changeBaseFiberedInGroupoids
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS)) :
    CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S' hS') :=
  ⟨changeBase B S S' hS hS' g 𝒳.val,
    (isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳.val).2 𝒳.2⟩

/-- The underlying category over the big fppf site of `S'` of `changeBaseFiberedInGroupoids 𝒳`
is `changeBase 𝒳.val`. -/
@[simp]
lemma changeBaseFiberedInGroupoids_val
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS)) :
    (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val =
      changeBase B S S' hS hS' g 𝒳.val :=
  rfl

/-! ### The scheme-valued points of Construction A -/

/-- A scheme-valued point of `𝒳` over the big fppf site of `S` is a scheme-valued point of
`changeBase 𝒳` over the big fppf site of `S'`, taken at the object of the site of `S'` with the
same underlying scheme and structure morphism composed with `g`. -/
lemma comp_changeBase_p_eq_map (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS) (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
    (hy : y ⋙ 𝒳.p = Over.map V.hom) :
    y ⋙ (changeBase B S S' hS hS' g 𝒳).p = Over.map (V.hom ≫ g) := by
  rw [changeBase_p, ← Functor.assoc, hy, Over.mapComp_eq]

/-- **The scheme-valued points of Construction A are those of the original category.** Every
scheme-valued point of `changeBase 𝒳` over the big fppf site of `S'` is a scheme-valued point of
`𝒳` over the big fppf site of `S`, on the same scheme, lying over a morphism to `S` whose
composite with `g` is the structure morphism of the point's base.

This is the content of the source's remark that the statement of Stacks 04X5 makes sense because
`j : (Sch/S)_{fppf} ⟶ (Sch/S')_{fppf}` is the localization functor at `S/S'`: no information about
the base is lost by Construction A. Together with
`AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` it matches up the quantifications over
scheme-valued points in the two sides of the algebraicity criterion. -/
@[stacks 04X5 "the scheme-valued points of Construction A"]
lemma exists_comp_p_eq_map_of_changeBase (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    (V' : BigFppfOver B S' hS') (y : BigFppfOver B V'.left.1 V'.left.2 ⥤ 𝒳.obj)
    (hy : y ⋙ (changeBase B S S' hS hS' g 𝒳).p = Over.map V'.hom) :
    ∃ h : V'.left ⟶ B.obj hS, y ⋙ 𝒳.p = Over.map h ∧ h ≫ g = V'.hom :=
  Over.exists_eq_map_of_comp_map g V'.hom (y ⋙ 𝒳.p) (by rw [Functor.assoc]; exact hy)

/-! ### Construction A on 1-morphisms, and representability by algebraic spaces -/

/-- Construction A on a 1-morphism of categories over the big fppf site of `S`: the same
underlying functor, read as a 1-morphism between the two categories over the big fppf site of
`S'`. -/
def changeBaseFunctor {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)} (f : 𝒳 ⥤ᵇ 𝒴) :
    changeBase B S S' hS hS' g 𝒳 ⥤ᵇ changeBase B S S' hS hS' g 𝒴 where
  toFunctor := f.toFunctor
  w := congrArg (fun q : 𝒳.obj ⥤ BigFppfOver B S hS => q ⋙ Over.map g) f.w

/-- The underlying functor of `changeBaseFunctor f` is that of `f`. -/
@[simp]
lemma changeBaseFunctor_toFunctor {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)} (f : 𝒳 ⥤ᵇ 𝒴) :
    (changeBaseFunctor B S S' hS hS' g f).toFunctor = f.toFunctor :=
  rfl

/-- **Stacks 02ZW is unchanged by Construction A.** A 1-morphism of categories over the big fppf
site of `S` is representable by algebraic spaces exactly when the 1-morphism over the big fppf
site of `S'` produced by Construction A is.

This is the second of the four clauses of Stacks 026O, in the form in which the clause is used:
the clause itself is this statement for the diagonal. The proof is the two halves of the source's
remark that `j : (Sch/S)_{fppf} ⟶ (Sch/S')_{fppf}` is the localization functor at `S/S'`. On
points it is `AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` and
`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`, which match up the quantifications
over scheme-valued points of the target. On 2-fibre products it is
`CategoryTheory.TwoFibreProductOver.fstEquivalenceOver`, which says that relocalizing the base
does not change the 2-fibre product of a point with the 1-morphism, as an equivalence over the
big fppf site of the point's scheme; so the representing algebraic space is literally the same on
both sides, and no transport of algebraicity along a comparison is needed. -/
@[stacks 04X5 "representability by algebraic spaces is unchanged by Construction A"]
theorem isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)} (f : 𝒳 ⥤ᵇ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S' hS' (changeBaseFunctor B S S' hS hS' g f) ↔
      IsRepresentableByAlgebraicSpaces B S hS f := by
  constructor
  · intro h
    dsimp only [IsRepresentableByAlgebraicSpaces] at h ⊢
    intro V y hy
    obtain ⟨F, hF, ⟨E⟩⟩ := h ((Over.map g).obj V) y
      (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴 V y hy)
    refine ⟨F, hF, ⟨?_⟩⟩
    simp only [Over.map_obj_hom, changeBase_p, changeBaseFunctor_toFunctor] at E
    exact TwoFibreProductOver.fstEquivalenceOver_trans g hy f.w E
  · intro h
    dsimp only [IsRepresentableByAlgebraicSpaces] at h ⊢
    intro V' y hy'
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴 V' y hy'
    obtain ⟨F, hF, ⟨E⟩⟩ := h (Over.mk h₀) y hy
    refine ⟨F, hF, ⟨?_⟩⟩
    simp only [changeBase_p, changeBaseFunctor_toFunctor]
    rw [← hg, Over.mapComp_eq]
    simp only [Over.mk_hom] at E
    exact TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.w E

/-! ### Surjectivity and Construction A -/

/-- **Being the spectrum of a field is unchanged by Construction A.** An object of the big fppf
site of `S`, read over the big fppf site of `S'`, has the same underlying scheme, so one of the
two is the spectrum of a field exactly when the other is. -/
lemma isFieldObject_overMap_iff (U : BigFppfOver B S hS) :
    IsFieldObject B S' hS' ((Over.map g).obj U) ↔ IsFieldObject B S hS U :=
  Iff.rfl

/-- **Stacks 06D4 is unchanged by Construction A.** A functor between two categories over the big
fppf site of `S`, strictly over that site, is surjective on objects exactly when it is surjective
on objects as a functor between the two categories over the big fppf site of `S'` produced by
Construction A.

Both the objects that have to be hit and the morphisms of the site along which they may be lifted
are unchanged. An object over `S` is the spectrum of a field exactly when it is one over `S'`
(`AlgebraicGeometry.Stack.isFieldObject_overMap_iff`); a lift over `S` gives a lift over `S'` by
`CategoryTheory.Functor.isHomLift_comp_map`; and conversely a lift `α` over `S'` is already a
lift over `S` along the canonical morphism assembled from `pY.map α`, whose source is the object
`pX.obj x` that the hypothesis `F ⋙ pY = pX` identifies with `pY.obj (F.obj x)`. -/
theorem isSurjectiveOnObjects_comp_overMap_iff
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) (Φ : X ⥤ Y)
    (hΦ : Φ ⋙ pY = pX) :
    IsSurjectiveOnObjects B S' hS' (pX ⋙ Over.map g) (pY ⋙ Over.map g) Φ ↔
      IsSurjectiveOnObjects B S hS pX pY Φ := by
  constructor
  · intro h U hU y hy
    obtain ⟨V', hV', f, x, hx, α, hα⟩ := h ((Over.map g).obj U)
      ((isFieldObject_overMap_iff B S S' hS hS' g U).2 hU) y (by
        simp only [Functor.comp_obj, hy])
    refine ⟨pX.obj x, ?_, eqToHom (Functor.congr_obj hΦ x).symm ≫ pY.map α ≫ eqToHom hy,
      x, rfl, α, ?_⟩
    · exact (isFieldObject_overMap_iff B S S' hS hS' g (pX.obj x)).1 (hx ▸ hV')
    · exact CategoryTheory.IsHomLift.of_fac pY _ α (Functor.congr_obj hΦ x) hy rfl
  · intro h U' hU' y hy
    subst hy
    obtain ⟨V, hV, f, x, hx, α, hα⟩ := h (pY.obj y)
      ((isFieldObject_overMap_iff B S S' hS hS' g (pY.obj y)).1 hU') y rfl
    refine ⟨(Over.map g).obj V, (isFieldObject_overMap_iff B S S' hS hS' g V).2 hV,
      (Over.map g).map f, x, ?_, α, ?_⟩
    · simp only [Functor.comp_obj, hx]
    · exact Functor.isHomLift_comp_map (g := g) pY f α hα

/-- **Construction A on a 1-morphism of the 2-category of categories fibred in groupoids over the
big fppf site of `S`.** This is `AlgebraicGeometry.Stack.changeBaseFunctor` on the underlying
based functor, read as a 1-morphism between the images of the source and target under
`AlgebraicGeometry.Stack.changeBaseFiberedInGroupoids`. -/
def changeBaseHom {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) :
    changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳 ⟶
      changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴 :=
  Bicategory.InducedBicategory.mkHom (changeBaseFunctor B S S' hS hS' g f.hom)

/-- **Stacks 06D4 is unchanged by Construction A**, for a 1-morphism of categories fibred in
groupoids. The underlying functor is unchanged and the two structure functors are composed with
`CategoryTheory.Over.map g`, so this is
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_comp_overMap_iff` for the based functor
underlying `f`. -/
theorem isSurjectiveOnObjects_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsSurjectiveOnObjects B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.p
        (CatFiberedInGroupoids.homFunctor (changeBaseHom B S S' hS hS' g f)) ↔
      IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) :=
  isSurjectiveOnObjects_comp_overMap_iff B S S' hS hS' g 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) f.hom.w

/-- **Relative surjectivity is unchanged by Construction A.** A 1-morphism of categories fibred
in groupoids over the big fppf site of `S` which is representable by algebraic spaces has the
relative property of Stacks 03YK for surjectivity of morphisms of algebraic spaces exactly when
the 1-morphism over the big fppf site of `S'` produced by Construction A has it.

This is the *surjectivity half of the presentation clause* of Stacks 026O, which is what Stacks
04X5 needs of it: that clause tests surjectivity and smoothness of the structural morphism of
every algebraic space representing a base change of the presentation along a scheme-valued point
of the stack, and for surjectivity that test is exactly
`AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.surjectiveMorphismProperty`.

No statement about the lower-shriek extension of Stacks 03I5 part (2) is needed. Stacks 06D7
replaces the relative test by surjectivity on objects, Stacks 06D4, which
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_changeBaseHom_iff` transfers directly. -/
@[stacks 04X5 "surjectivity of the presentation is unchanged by Construction A"]
theorem hasRelativeProperty_surjective_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasRelativeProperty.{u, v, w, vP} B S' hS' (Space.surjectiveMorphismProperty B S' hS')
        (changeBaseHom B S S' hS hS' g f)
        ((isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f.hom).2 hf) ↔
      HasRelativeProperty.{u, v, w, vP} B S hS (Space.surjectiveMorphismProperty B S hS) f hf :=
  (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, v, w, vP} B S' hS'
        (changeBaseHom B S S' hS hS' g f)
        ((isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
          f.hom).2 hf)).symm.trans
    ((isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g f).trans
      (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, v, w, vP} B S hS f hf))

/-! ### Smoothness and Construction A -/

/-- **A relative property tested on étale charts is unchanged by Construction A.** Let `Q` be a
property of morphisms of schemes. A 1-morphism of categories fibred in groupoids over the big
fppf site of `S` which is representable by algebraic spaces has the relative property of
Stacks 03YK at the every-étale-chart condition of Stacks 03MJ for `Q` exactly when the 1-morphism
over the big fppf site of `S'` produced by Construction A has it.

At `Q = AlgebraicGeometry.Smooth` this is the *smoothness half of the presentation clause* of
Stacks 026O, the other half being
`AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff`; that case is recovered
by applying this statement to `@AlgebraicGeometry.Smooth`, since
`AlgebraicGeometry.Space.smoothMorphismProperty` *is* the every-étale-chart condition at
`AlgebraicGeometry.Smooth`. It is stated at a general `Q` because that is what the separation
axioms of Stacks 04YW need of it: for instance
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` is the every-étale-chart condition at
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`, and nothing in the
argument is about smoothness.

The relative property is written out as the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` rather than through that abbreviation, exactly as
`AlgebraicGeometry.Stack.relativeProperty_baseChange` and
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` do: the abbreviation carries
`[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]`
as instance arguments and neither is available for a general `Q`, while its body uses neither, so
the quantifier is the same proposition carrying no hypothesis on the property.

Unlike surjectivity this really is a statement about the lower-shriek extension of Stacks 03I5
part (2), since smoothness has no objects-level criterion. The two quantifications match up by
`AlgebraicGeometry.Stack.comp_changeBase_p_eq_map` and
`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase` on scheme-valued points and by
`CategoryTheory.TwoFibreProductOver.fstEquivalenceOver` on 2-fibre products, exactly as in
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`; so the
representing algebraic space is the same object on both sides, living over the same scheme over
`S`, and what is left is that its structural morphism has `Q` on every étale chart over `S`
exactly when it does over `S'`. That is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`: the
every-étale-chart condition of Stacks 03MJ for the structural morphism of the image of Stacks
04SG's forward functor does not depend on the base at all. -/
@[stacks 04X5 "smoothness of the presentation is unchanged by Construction A"]
theorem hasRelativeProperty_smooth_changeBaseHom_iff (Q : MorphismProperty Scheme.{u})
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (_hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    (∀ (U : BigFppfOver B S' hS')
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.obj)
        (_hy : y ⋙ (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
            (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.p y
            (CatFiberedInGroupoids.homFunctor (changeBaseHom B S S' hS hS' g f)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.HoldsOnEveryEtaleChart B S' hS' Q
          (algebraicSpaceMap B S' hS' U
            ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj
              ⟨F, hF⟩)).hom) ↔
      (∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.HoldsOnEveryEtaleChart B S hS Q
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
              ⟨F, hF⟩)).hom) := by
  constructor
  · rintro hbig U y hy F hF ⟨E⟩
    exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl Q F hF).1 (hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩)
  · rintro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg Q F hF).2
        (hsmall (Over.mk h₀) y hy F hF
          ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩)

/-- Surjectivity and smoothness of the relative property are both unchanged by Construction A. -/
private theorem hasRelativeProperty_surjective_and_smooth_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hf' : IsRepresentableByAlgebraicSpaces B S' hS' (changeBaseHom B S S' hS hS' g f).hom) :
    (HasRelativeProperty.{u, v, w, vP} B S' hS' (Space.surjectiveMorphismProperty B S' hS')
        (changeBaseHom B S S' hS hS' g f) hf' ∧
      HasRelativeProperty.{u, v, w, vP} B S' hS' (Space.smoothMorphismProperty B S' hS')
        (changeBaseHom B S S' hS hS' g f) hf') ↔
    (HasRelativeProperty.{u, v, w, vP} B S hS (Space.surjectiveMorphismProperty B S hS) f hf ∧
      HasRelativeProperty.{u, v, w, vP} B S hS (Space.smoothMorphismProperty B S hS) f hf) :=
  and_congr (hasRelativeProperty_surjective_changeBaseHom_iff.{u, v, w, vP} B S S' hS hS' g f hf)
    (hasRelativeProperty_smooth_changeBaseHom_iff B S S' hS hS' g
      (@AlgebraicGeometry.Smooth.{u}) f hf)

/-! ### The diagonal and Construction A -/

/-- **A scheme-valued point of `changeBase 𝒳` over `S'` is a scheme-valued point of `𝒳` over `S`,
viewed over `S'`.** For a factorization `h` through `S` of the structure morphism of an object `U'`
of the big fppf site of `S'`, the slice of that site over `U'` is isomorphic to the slice of the
big fppf site of `S` over `(U'.left, h)`, compatibly with the structure functors: both slices are
the big fppf site of `U'.left`, by `CategoryTheory.Over.iteratedSliceEquiv`.

This is the comparison in the direction that the backward implication of
`AlgebraicGeometry.Stack.isRepresentableFromSchemes_changeBase_iff` composes with. -/
def factorSliceFunctor {U' : BigFppfOver B S' hS'} {h : U'.left ⟶ B.obj hS}
    (hh : h ≫ g = U'.hom) :
    (changeBaseFiberedInGroupoids B S S' hS hS' g
        (schemeFibredCategory B S hS (Over.mk h))).val ⥤ᵇ
      (schemeFibredCategory B S' hS' U').val where
  toFunctor := Over.iteratedSliceForward (Over.mk h) ⋙ Over.iteratedSliceBackward U'
  w := by
    have h1 : Over.iteratedSliceBackward U' ⋙ Over.forget U' = Over.map U'.hom :=
      Over.iteratedSliceBackward_forget U'
    have h2 : Over.iteratedSliceForward (Over.mk h : BigFppfOver B S hS) ⋙ Over.map h
        = Over.forget (Over.mk h) :=
      Over.iteratedSliceForward_comp_map (Over.mk h)
    change (Over.iteratedSliceForward (Over.mk h) ⋙ Over.iteratedSliceBackward U') ⋙
      Over.forget U' = Over.forget (Over.mk h) ⋙ Over.map g
    rw [Functor.assoc, h1, ← hh, Over.mapComp_eq, ← Functor.assoc, h2]

/-- `AlgebraicGeometry.Stack.factorSliceFunctor` read in the other direction, for the object `U'`
of the big fppf site of `S'` produced by Construction A out of an object `V` of the big fppf site
of `S`. It is stated separately rather than as an inverse because the two implications of
`AlgebraicGeometry.Stack.isRepresentableFromSchemes_changeBase_iff` each need the comparison in
only one direction, and taking it that way makes both comparison isomorphisms the identity. -/
def factorSliceInverse (V : BigFppfOver B S hS) :
    (schemeFibredCategory B S' hS' ((Over.map g).obj V)).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS V)).val where
  toFunctor := Over.iteratedSliceForward ((Over.map g).obj V) ⋙ Over.iteratedSliceBackward V
  w := by
    have h1 : Over.iteratedSliceBackward V ⋙ (Over.forget V ⋙ Over.map g)
        = Over.map V.hom ⋙ Over.map g := by
      rw [← Functor.assoc, Over.iteratedSliceBackward_forget]
    change (Over.iteratedSliceForward ((Over.map g).obj V) ⋙ Over.iteratedSliceBackward V) ⋙
      (Over.forget V ⋙ Over.map g) = Over.forget ((Over.map g).obj V)
    rw [Functor.assoc, h1, ← Over.mapComp_eq]
    exact Over.iteratedSliceForward_comp_map ((Over.map g).obj V)

/-- The underlying functor of `AlgebraicGeometry.Stack.factorSliceFunctor` is an equivalence of
categories. -/
instance isEquivalence_factorSliceFunctor {U' : BigFppfOver B S' hS'}
    {h : U'.left ⟶ B.obj hS} (hh : h ≫ g = U'.hom) :
    Functor.IsEquivalence (factorSliceFunctor B S S' hS hS' g hh).toFunctor := by
  change Functor.IsEquivalence
    (Over.iteratedSliceForward (Over.mk h) ⋙ Over.iteratedSliceBackward U')
  have _ : Functor.IsEquivalence (Over.iteratedSliceForward (Over.mk h : BigFppfOver B S hS)) :=
    inferInstanceAs (Functor.IsEquivalence (Over.iteratedSliceEquiv
      (Over.mk h : BigFppfOver B S hS)).functor)
  have _ : Functor.IsEquivalence (Over.iteratedSliceBackward U') :=
    inferInstanceAs (Functor.IsEquivalence (Over.iteratedSliceEquiv U').inverse)
  infer_instance

/-- The underlying functor of `AlgebraicGeometry.Stack.factorSliceInverse` is an equivalence of
categories. -/
instance isEquivalence_factorSliceInverse (V : BigFppfOver B S hS) :
    Functor.IsEquivalence (factorSliceInverse B S S' hS hS' g V).toFunctor := by
  change Functor.IsEquivalence
    (Over.iteratedSliceForward ((Over.map g).obj V) ⋙ Over.iteratedSliceBackward V)
  have _ : Functor.IsEquivalence (Over.iteratedSliceForward ((Over.map g).obj V)) :=
    inferInstanceAs (Functor.IsEquivalence
      (Over.iteratedSliceEquiv ((Over.map g).obj V)).functor)
  have _ : Functor.IsEquivalence (Over.iteratedSliceBackward V) :=
    inferInstanceAs (Functor.IsEquivalence (Over.iteratedSliceEquiv V).inverse)
  infer_instance

/-- The structure morphism of an object `U'` of the big fppf site of `S'` admitting a 1-morphism
to `changeBase 𝒳` from the category it represents factors through `g`, along a morphism `h` over
which that 1-morphism, read on the big fppf site of `U'.left`, lies. -/
theorem exists_iteratedSliceBackward_comp_p_eq_map
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)} {U' : BigFppfOver B S' hS'}
    (x : (schemeFibredCategory B S' hS' U').val ⥤ᵇ changeBase B S S' hS hS' g 𝒳) :
    ∃ h : U'.left ⟶ B.obj hS,
      Over.iteratedSliceBackward U' ⋙ x.toFunctor ⋙ 𝒳.p = Over.map h ∧ h ≫ g = U'.hom := by
  have hx : x.toFunctor ⋙ (𝒳.p ⋙ Over.map g) = Over.forget U' := x.w
  exact Over.exists_eq_map_of_comp_map g U'.hom
    (Over.iteratedSliceBackward U' ⋙ x.toFunctor ⋙ 𝒳.p)
    ((congrArg (Over.iteratedSliceBackward U' ⋙ ·) hx).trans
      (Over.iteratedSliceBackward_forget U'))

/-- A 1-morphism to `changeBase 𝒳` from the category represented by an object `U'` of the big
fppf site of `S'`, read as a 1-morphism to `𝒳` from the category represented by `(U'.left, h)`
for a factorization `h` through `S` over which it lies. -/
def factorSlicePoint {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)} {U' : BigFppfOver B S' hS'}
    (x : (schemeFibredCategory B S' hS' U').val ⥤ᵇ changeBase B S S' hS hS' g 𝒳)
    {h : U'.left ⟶ B.obj hS}
    (hF : Over.iteratedSliceBackward U' ⋙ x.toFunctor ⋙ 𝒳.p = Over.map h) :
    (schemeFibredCategory B S hS (Over.mk h)).val ⥤ᵇ 𝒳 where
  toFunctor := Over.iteratedSliceForward (Over.mk h) ⋙
    (Over.iteratedSliceBackward U' ⋙ x.toFunctor)
  w := by
    change Over.iteratedSliceForward (Over.mk h) ⋙
        (Over.iteratedSliceBackward U' ⋙ x.toFunctor ⋙ 𝒳.p) = Over.forget (Over.mk h)
    rw [hF]
    exact Over.iteratedSliceForward_comp_map (Over.mk h)

/-- Precomposition with an equivalence of sources preserves representability by algebraic spaces
(Stacks 0457), with the identity as comparison isomorphism. -/
private theorem isRepresentableByAlgebraicSpaces_comp_iff
    {𝒳' : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S' hS')}
    {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, t₂} (BigFppfOver B S' hS')}
    {𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S' hS')}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (a : 𝒳'.val ⥤ᵇ 𝒳.val) [Functor.IsEquivalence a.toFunctor] :
    IsRepresentableByAlgebraicSpaces B S' hS' f ↔
      IsRepresentableByAlgebraicSpaces B S' hS' (BasedFunctor.comp a f) :=
  isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS' f _ a (Iso.refl _)

/-- **Condition (3) of Stacks 045G is unchanged by Construction A.** Every 1-morphism to `𝒳` from
the category represented by a scheme over `S` is representable by algebraic spaces exactly when
every 1-morphism to `changeBase 𝒳` from the category represented by a scheme over `S'` is.

This is where the asymmetry of Construction A is absorbed. A 1-morphism from the category
represented by a scheme `U'` over `S'` into `changeBase 𝒳` forces the structure morphism of `U'`
to factor through `S`, by the rigidity of relocalization
(`CategoryTheory.Over.exists_eq_map_of_comp_map`): so there is no quantification over objects of
the site of `S'` that do not come from the site of `S`, and no equalizer argument is needed. Given
such a factorization the two slices are identified by
`AlgebraicGeometry.Stack.factorSliceFunctor`, and the statement is then
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff` together with
Stacks 0457 in the source variable
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source`). Both
implications use the comparison in the direction that makes the comparison isomorphism of 0457 the
identity. -/
theorem isRepresentableFromSchemes_changeBase_iff
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    IsRepresentableFromSchemes B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) ↔
      IsRepresentableFromSchemes B S hS 𝒳 := by
  constructor
  · intro hbig U x₀
    refine (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g x₀).1 ?_
    exact (isRepresentableByAlgebraicSpaces_comp_iff B S' hS'
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFunctor B S S' hS hS' g x₀) (factorSliceInverse B S S' hS hS' g U)).2
      (hbig _ _)
  · intro hsmall U' x
    obtain ⟨h, hF, hh⟩ := exists_iteratedSliceBackward_comp_p_eq_map B S S' hS hS' g
      (𝒳 := 𝒳.val) x
    let x₀ : (schemeFibredCategory B S hS (Over.mk h)).val ⥤ᵇ 𝒳.val :=
      factorSlicePoint B S S' hS hS' g (𝒳 := 𝒳.val) x hF
    exact (isRepresentableByAlgebraicSpaces_comp_iff B S' hS'
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) x
      (factorSliceFunctor B S S' hS hS' g hh)).2
      ((isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g x₀).2
        (hsmall (Over.mk h) x₀))

/-- **The diagonal clause of Stacks 026O is unchanged by Construction A.** The diagonal of a
category fibred in groupoids over the big fppf site of `S` is representable by algebraic spaces
exactly when the diagonal of the category over the big fppf site of `S'` produced by Construction
A is.

The two diagonals are *not* comparable directly: the self-product of `changeBase 𝒳` over the big
fppf site of `S'` has the strictly larger object set of pairs lying over a common `S'`-scheme by
two different morphisms to `S`, so there is no equivalence to transport along. The route taken
instead is Stacks 045G: by its conditions (1), (2) and (3) the clause is equivalent to
`AlgebraicGeometry.Stack.IsRepresentableFromSchemes`, which does transfer
(`AlgebraicGeometry.Stack.isRepresentableFromSchemes_changeBase_iff`), because a 1-morphism out
of a scheme-valued point sees only one morphism to `S` at a time. The equalizer of the two
morphisms, which a direct comparison of the self-products would have to form, is absorbed into the
already-proved equivalence of conditions (2) and (3). -/
@[stacks 04X5 "representability of the diagonal is unchanged by Construction A"]
theorem isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    IsRepresentableByAlgebraicSpaces B S' hS'
        (diagonalBasedFunctor B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)) ↔
      IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳) :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)).trans
    ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)).trans
      ((isRepresentableFromSchemes_changeBase_iff B S S' hS hS' g 𝒳).trans
        ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).symm.trans
          (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).symm)))

/-! ### The two inputs of the stack clause -/

/-- **A covering family of the big fppf site of `S'` is jointly epimorphic.** Two morphisms out
of the underlying scheme of the target of a covering family which agree after composition with
every member of the family are equal.

This is separatedness of the representable presheaf of the target, which holds because the fppf
topology of a big fppf site is subcanonical
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`). It is what identifies the two morphisms
to `S` that an object of the big fppf site of `S'` can carry when it is the base of two objects
of the
total category of `changeBase 𝒳`. -/
theorem eq_of_isCovering {U' : BigFppfOver B S' hS'} {I : Type w}
    (Z : I → BigFppfOver B S' hS') (f : ∀ i, Z i ⟶ U')
    (hf : Sieve.ofArrows Z f ∈ BigFppfOver.topology B S' hS' U')
    {T : B.Schemes} (a b : U'.left ⟶ T)
    (hab : ∀ i, (f i).left ≫ a = (f i).left ≫ b) : a = b :=
  have _ := BigFppfSite.subcanonical_topology B
  Over.eq_of_mem_over B.topology Z f hf a b hab

/-- **A point of the big fppf site of `S'` covered by points coming from the site of `S` comes
from the site of `S` itself.** If the structure morphism of every member of a covering family of
`U'` factors through `g`, and the factorizations agree on every pair of morphisms into two
members agreeing over `U'`, then the structure morphism of `U'` factors through `g`, compatibly
with the given factorizations, and the factorization is unique by
`AlgebraicGeometry.Stack.eq_of_isCovering`.

This is the descent input of the stack-in-groupoids clause of Stacks 026O for Construction A: an
object of the total category of `changeBase 𝒳` lying over `U'` lies over an object of the big
fppf site of `S`, so gluing objects along a covering family of `U'` is only possible when
`U'.hom` itself factors through `g`, and nothing short of the sheaf condition for the
representable presheaf of `S` on the big fppf site produces that factorization. -/
@[stacks 04X5 "the descent input of the stack clause of Construction A"]
theorem exists_factorization_of_isCovering {U' : BigFppfOver B S' hS'} {I : Type w}
    (Z : I → BigFppfOver B S' hS') (f : ∀ i, Z i ⟶ U')
    (hf : Sieve.ofArrows Z f ∈ BigFppfOver.topology B S' hS' U')
    (a : ∀ i, (Z i).left ⟶ B.obj hS) (ha : ∀ i, a i ≫ g = (Z i).hom)
    (hcompat : ∀ (i j : I) (Y : B.Schemes) (u : Y ⟶ (Z i).left) (v : Y ⟶ (Z j).left),
      u ≫ (f i).left = v ≫ (f j).left → u ≫ a i = v ≫ a j) :
    ∃ h : U'.left ⟶ B.obj hS, h ≫ g = U'.hom ∧ ∀ i, (f i).left ≫ h = a i :=
  have _ := BigFppfSite.subcanonical_topology B
  Over.exists_factorization_of_mem_over B.topology g Z f hf a ha hcompat

/-! ### The stack clause and Construction A -/

/-- **The stack-in-groupoids clause of Stacks 026O transfers back along Construction A.** If the
category over the big fppf site of `S'` produced by Construction A is a stack in groupoids for
the fppf topology there, then the original category over the big fppf site of `S` is a stack in
groupoids for the fppf topology of that site.

This is one of the two implications of the third of the four clauses of Stacks 026O. Every piece
of data over the site of `S` is read over the site of `S'` — covering families by
`CategoryTheory.Over.mem_over_map_iff`, the fibre-product overlaps by
`CategoryTheory.Over.isPullback_map_iff`, restrictions by
`CategoryTheory.Functor.Restriction.overMap`, and descent data field by field — the hypothesis is
applied there, and the conclusion is read back. The one step that is not formal is the object of
the site of `S` that a glued object lies over: the hypothesis produces an object lying over the
image of `U`, which determines its structure morphism only after composition with every member of
the covering family, so `AlgebraicGeometry.Stack.eq_of_isCovering` is used to identify it
with `U`.

The converse implication is
`AlgebraicGeometry.Stack.isStackInGroupoids_changeBase`, and the two together are
`AlgebraicGeometry.Stack.isStackInGroupoids_changeBase_iff`. -/
@[stacks 04X5 "the stack clause transfers back along Construction A"]
theorem isStackInGroupoids_of_changeBase (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    (h : (changeBase B S S' hS hS' g 𝒳).p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S' hS')) :
    𝒳.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) :=
  have _ := BigFppfSite.subcanonical_topology B
  Functor.isStackInGroupoids_of_comp_overMap 𝒳.p g B.topology h

/-- **The stack-in-groupoids clause of Stacks 026O transfers along Construction A.** If a
category over the big fppf site of `S` is a stack in groupoids for the fppf topology there, then
the category over the big fppf site of `S'` produced by Construction A is a stack in groupoids
for the fppf topology of that site.

This is the converse of `AlgebraicGeometry.Stack.isStackInGroupoids_of_changeBase`, and it is the
direction that needs the gluing input: an object of the total category lying over an object `U'`
of the site of `S'` lies over an object of the site of `S`, that is, over a *factorization* of
`U'.hom` through `g`, and two factorizations need not be equal. For the `Isom` sheaf condition
the two factorizations carried by the two given objects agree after composition with every member
of the covering family, so `AlgebraicGeometry.Stack.eq_of_isCovering` identifies them; for
effective descent no factorization of `U'.hom` is given at all, and
`AlgebraicGeometry.Stack.exists_factorization_of_isCovering` glues one out of those carried by
the members of the covering family. -/
theorem isStackInGroupoids_changeBase (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    (h : 𝒳.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S' hS') :=
  have _ := BigFppfSite.subcanonical_topology B
  Functor.isStackInGroupoids_comp_overMap 𝒳.p g B.topology h

/-- **The stack-in-groupoids clause of Stacks 026O is unchanged by Construction A.** A category
over the big fppf site of `S` is a stack in groupoids for the fppf topology there exactly when
the category over the big fppf site of `S'` produced by Construction A is a stack in groupoids
for the fppf topology of that site.

This is the third of the four clauses of Stacks 026O, in full. The clause is read entirely in the
two localized fppf topologies: a covering family of the site of `S` is one of the site of `S'`
and conversely (`CategoryTheory.Over.mem_over_map_iff` and
`CategoryTheory.Over.mem_over_mk`), and the fibre-product overlaps, the restrictions, the fibre
isomorphisms and the descent data all match. The one non-formal ingredient is subcanonicity of
the fppf topology, `AlgebraicGeometry.BigFppfSite.subcanonical_topology`, which is what pins
down the morphism to `S` carried by an object of the site of `S'`. -/
@[stacks 04X5 "the stack clause of Stacks 026O is unchanged by Construction A"]
theorem isStackInGroupoids_changeBase_iff (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p.IsStackInGroupoids.{w}
        (BigFppfOver.topology B S' hS') ↔
      𝒳.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) :=
  ⟨isStackInGroupoids_of_changeBase B S S' hS hS' g 𝒳,
    isStackInGroupoids_changeBase B S S' hS hS' g 𝒳⟩

/-! ### The sieve-indexed stack clause and Construction A -/

/-- **The sieve-indexed stack clause of Stacks 026F is unchanged by Construction A.** A category
over the big fppf site of `S` is a stack in the sense of Stacks 026F for the fppf topology there
exactly when the category over the big fppf site of `S'` produced by Construction A is one for
the fppf topology of that site.

Unlike the family-indexed condition this needs no transfer of covering families and descent data
at all: both sides are read through the single statement that the composite of the structure
functor with the localization functor of the big fppf site of `S` is a stack over the whole big
fppf site, by Constructions A and B of Stacks 04WV
(`CategoryTheory.Over.isStack_map_iff`). Subcanonicity of the fppf topology
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`) supplies the sheaf hypothesis of those two
constructions for the representable presheaves of `S` and of `S'`.

The universes are those of Stacks 04X5 itself: Construction B relates two categories over the
same site in the *same* universes, so the total category is taken in the object universe one
above the scheme universe, which is what `AlgebraicGeometry.Stack.IsAlgebraicStack` is applied
at. -/
@[stacks 04X5 "the sieve-indexed stack clause of Stacks 026O is unchanged by Construction A"]
theorem isStack_changeBase_iff (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p.IsStack (BigFppfOver.topology B S' hS') ↔
      𝒳.p.IsStack (BigFppfOver.topology B S hS) :=
  have _ := BigFppfSite.subcanonical_topology B
  Over.isStack_map_iff.{u, u, u + 1, u} g 𝒳.p

/-! ### The presentation clause as a pair of relative properties -/

/-- **The presentation clause of Stacks 026O is the conjunction of two instances of Stacks
03YK.** Surjectivity and smoothness of the structural morphism of every algebraic space
representing a base change of a 1-morphism along a scheme-valued point of its target — the
condition `AlgebraicGeometry.Stack.IsAlgebraicStack` spells out for its presentation — is
`AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.surjectiveMorphismProperty` together with the same at
`AlgebraicGeometry.Space.smoothMorphismProperty`.

Both morphism properties are abbreviations for the corresponding condition on the underlying
morphism of presheaves, so the only content is that a universally quantified conjunction is the
conjunction of the universally quantified conjuncts. The representability hypothesis is not used
by either side; it is present because Stacks 03YK carries it. -/
theorem forall_isSurjective_and_isSmooth_iff_hasRelativeProperty
    {𝒵 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒵.val ⥤ᵇ 𝒴.val) (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    (∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒵.val.p 𝒴.val.p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let m := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor
            B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS m ∧ Space.IsSmooth B S hS m)) ↔
      HasRelativeProperty.{u, v, w, vP} B S hS (Space.surjectiveMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom f) hf ∧
        HasRelativeProperty.{u, v, w, vP} B S hS (Space.smoothMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom f) hf := by
  constructor
  · intro h
    exact ⟨fun V y hy F hF hE => (h V y hy F hF hE).1,
      fun V y hy F hF hE => (h V y hy F hF hE).2⟩
  · intro h V y hy F hF hE
    exact ⟨h.1 V y hy F hF hE, h.2 V y hy F hF hE⟩

/-- **Stacks 03YK is unchanged by an equivalence of the source.** A 1-morphism of categories
fibred in groupoids over the big fppf site of `S` which is representable by algebraic spaces has
the relative property `P` exactly when its composite with an equivalence of sources over the site
has it.

This is the source half of Stacks 0457 for a predicate that quantifies over the *representatives*
of the first projection of the 2-fibre product rather than over their existence: the two
projections are themselves equivalent over the site of the scheme-valued point, by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_precompose_source`, so composing with that
equivalence matches up the two hypotheses of Stacks 03YK while leaving its conclusion — which
mentions only the point and the representing algebraic space — untouched. -/
theorem hasRelativeProperty_iff_of_equivalence_source
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒵' 𝒵 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒵.val ⥤ᵇ 𝒴.val) (a : 𝒵'.val ⥤ᵇ 𝒵.val)
    [Functor.IsEquivalence a.toFunctor]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp a f)) :
    HasRelativeProperty.{u, v, w, vP} B S hS P
        (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp a f)) hf' ↔
      HasRelativeProperty.{u, v, w, vP} B S hS P
        (Bicategory.InducedBicategory.mkHom f) hf := by
  have key : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj),
      y ⋙ 𝒴.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒵'.val.p 𝒴.val.p y
          (a.toFunctor ⋙ f.toFunctor))
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒵.val.p 𝒴.val.p y f.toFunctor)) :=
    fun V y hy => nonempty_equivalenceOver_fst_precompose_source V.hom y f.toFunctor
      a.toFunctor 𝒵'.isFiberedInGroupoids 𝒵.isFiberedInGroupoids
      𝒴.isFiberedInGroupoids a.w hy f.w
  constructor
  · rintro h V y hy F hF ⟨E⟩
    obtain ⟨e⟩ := key V y hy
    exact h V y hy F hF ⟨e.trans E⟩
  · rintro h V y hy F hF ⟨E⟩
    obtain ⟨e⟩ := key V y hy
    exact h V y hy F hF ⟨e.symm.trans E⟩


/-- The presentation clause (surjective and smooth relative properties) is unchanged by an
equivalence of the source. -/
private theorem hasRelativeProperty_surjective_and_smooth_iff_of_equivalence_source
    {𝒵' 𝒵 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒵.val ⥤ᵇ 𝒴.val) (a : 𝒵'.val ⥤ᵇ 𝒵.val) [Functor.IsEquivalence a.toFunctor]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp a f)) :
    (HasRelativeProperty.{u, v, w, vP} B S hS (Space.surjectiveMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp a f)) hf' ∧
      HasRelativeProperty.{u, v, w, vP} B S hS (Space.smoothMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp a f)) hf') ↔
    (HasRelativeProperty.{u, v, w, vP} B S hS (Space.surjectiveMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom f) hf ∧
      HasRelativeProperty.{u, v, w, vP} B S hS (Space.smoothMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom f) hf) :=
  and_congr (hasRelativeProperty_iff_of_equivalence_source B S hS _ f a hf hf')
    (hasRelativeProperty_iff_of_equivalence_source B S hS _ f a hf hf')

/-! ### The algebraicity criterion -/

/-- The forward direction of `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`: a
category over the big fppf site of `S` that Construction A carries to an algebraic stack over `S'`
is an algebraic stack over `S`. -/
theorem isAlgebraicStack_of_isAlgebraicStack_changeBase
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w} B S' hS' (changeBase B S S' hS hS' g 𝒳)) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  obtain ⟨h𝒳', ⟨hsv, hsg⟩, hdiag, U', f', hf', hpres⟩ := h
  have h𝒳 := (isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).1 h𝒳'
  refine ⟨h𝒳, ⟨(isStack_changeBase_iff B S S' hS hS' g 𝒳).1 hsv,
      (isStackInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).1 hsg⟩,
    (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff B S S' hS hS' g
      (CatFiberedInGroupoids.mk 𝒳 h𝒳)).1 hdiag, ?_⟩
  obtain ⟨c, hc, hcg⟩ := exists_iteratedSliceBackward_comp_p_eq_map B S S' hS hS' g
    (𝒳 := 𝒳) f'
  let x₀ : (schemeFibredCategory B S hS (Over.mk c)).val ⥤ᵇ
      (CatFiberedInGroupoids.mk 𝒳 h𝒳).val :=
    factorSlicePoint B S S' hS hS' g (𝒳 := 𝒳) f' hc
  have hcomp : IsRepresentableByAlgebraicSpaces B S' hS'
      (BasedFunctor.comp (factorSliceFunctor B S S' hS hS' g hcg) f') :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS'
      (𝒳' := changeBaseFiberedInGroupoids B S S' hS hS' g
        (schemeFibredCategory B S hS (Over.mk c)))
      (𝒳 := schemeFibredCategory B S' hS' U')
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g
        (CatFiberedInGroupoids.mk 𝒳 h𝒳))
      (f := f') (f' := BasedFunctor.comp (factorSliceFunctor B S S' hS hS' g hcg) f')
      (a := factorSliceFunctor B S S' hS hS' g hcg) (α := Iso.refl _)).1 hf'
  have hx₀ : IsRepresentableByAlgebraicSpaces B S hS x₀ :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g x₀).1 hcomp
  refine ⟨Over.mk c, x₀, hx₀, ?_⟩
  refine (forall_isSurjective_and_isSmooth_iff_hasRelativeProperty.{u, u, u + 1, u} B S hS
    (𝒵 := schemeFibredCategory B S hS (Over.mk c))
    (𝒴 := CatFiberedInGroupoids.mk 𝒳 h𝒳) x₀ hx₀).2 ?_
  refine (hasRelativeProperty_surjective_and_smooth_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS
    hS' g (Bicategory.InducedBicategory.mkHom x₀) hx₀ hcomp).1 ?_
  exact (hasRelativeProperty_surjective_and_smooth_iff_of_equivalence_source.{u, u, u + 1, u} B S'
    hS' (𝒵' := changeBaseFiberedInGroupoids B S S' hS hS' g
      (schemeFibredCategory B S hS (Over.mk c)))
    (𝒵 := schemeFibredCategory B S' hS' U')
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g (CatFiberedInGroupoids.mk 𝒳 h𝒳))
    f' (factorSliceFunctor B S S' hS hS' g hcg) hf' hcomp).2
    ((forall_isSurjective_and_isSmooth_iff_hasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (𝒵 := schemeFibredCategory B S' hS' U')
      (𝒴 := CatFiberedInGroupoids.mk (changeBase B S S' hS hS' g 𝒳) h𝒳') f' hf').1 hpres)

/-- The backward direction of `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`:
Construction A carries an algebraic stack over `S` to an algebraic stack over `S'`. -/
theorem isAlgebraicStack_changeBase_of_isAlgebraicStack
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    IsAlgebraicStack.{u, w} B S' hS' (changeBase B S S' hS hS' g 𝒳) := by
  obtain ⟨h𝒳, ⟨hsv, hsg⟩, hdiag, U, f, hf, hpres⟩ := h
  have h𝒳' := (isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 h𝒳
  refine ⟨h𝒳', ⟨(isStack_changeBase_iff B S S' hS hS' g 𝒳).2 hsv,
      (isStackInGroupoids_changeBase_iff B S S' hS hS' g 𝒳).2 hsg⟩,
    (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff B S S' hS hS' g
      (CatFiberedInGroupoids.mk 𝒳 h𝒳)).2 hdiag, ?_⟩
  have h₁ : IsRepresentableByAlgebraicSpaces B S' hS'
      (changeBaseFunctor B S S' hS hS' g f) :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f).2 hf
  have h₂ := (isRepresentableByAlgebraicSpaces_comp_iff B S' hS'
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g (CatFiberedInGroupoids.mk 𝒳 h𝒳))
    (changeBaseFunctor B S S' hS hS' g f) (factorSliceInverse B S S' hS hS' g U)).1 h₁
  refine ⟨(Over.map g).obj U, BasedFunctor.comp (factorSliceInverse B S S' hS hS' g U)
    (changeBaseFunctor B S S' hS hS' g f), h₂, ?_⟩
  refine (forall_isSurjective_and_isSmooth_iff_hasRelativeProperty.{u, u, u + 1, u} B S' hS'
    (𝒵 := schemeFibredCategory B S' hS' ((Over.map g).obj U))
    (𝒴 := CatFiberedInGroupoids.mk (changeBase B S S' hS hS' g 𝒳) h𝒳')
    (BasedFunctor.comp (factorSliceInverse B S S' hS hS' g U)
      (changeBaseFunctor B S S' hS hS' g f)) h₂).2 ?_
  refine (hasRelativeProperty_surjective_and_smooth_iff_of_equivalence_source.{u, u, u + 1, u}
    B S' hS' (𝒵' := schemeFibredCategory B S' hS' ((Over.map g).obj U))
    (𝒵 := changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS U))
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g (CatFiberedInGroupoids.mk 𝒳 h𝒳))
    (changeBaseFunctor B S S' hS hS' g f) (factorSliceInverse B S S' hS hS' g U) h₁ h₂).2 ?_
  exact (hasRelativeProperty_surjective_and_smooth_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS
    hS' g (Bicategory.InducedBicategory.mkHom f) hf h₁).2
    ((forall_isSurjective_and_isSmooth_iff_hasRelativeProperty.{u, u, u + 1, u} B S hS
      (𝒵 := schemeFibredCategory B S hS U)
      (𝒴 := CatFiberedInGroupoids.mk 𝒳 h𝒳) f hf).1 hpres)

/-- **The algebraicity criterion of Stacks 04X5.** A category over the big fppf site of `S` is an
algebraic stack over `S` exactly when the category over the big fppf site of `S'` produced by
Construction A is an algebraic stack over `S'`. Together with the object, 1-morphism and
2-morphism equivalences of Stacks 04WV this is what restricts that isomorphism of 2-categories to
algebraic stacks.

`AlgebraicGeometry.Stack.IsAlgebraicStack` is not a conjunction of the four clauses of Stacks
026O: the fibred-in-groupoids clause is existentially quantified ahead of the others, which are
stated for the bundled category fibred in groupoids it produces. So the witness is transported
first, by `AlgebraicGeometry.Stack.isFiberedInGroupoids_changeBase_iff`, and the bundled object on
the `S'` side is then `AlgebraicGeometry.Stack.changeBaseFiberedInGroupoids` of the bundled object
on the `S` side — the same underlying category over the site, paired with a proof of a
proposition, so the two agree definitionally and the remaining clauses can be transported one by
one:

* the stack clause is `AlgebraicGeometry.Stack.isStack_changeBase_iff` in its sieve-indexed half
  and `AlgebraicGeometry.Stack.isStackInGroupoids_changeBase_iff` in its family-indexed half;
* the diagonal clause is
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`;
* the presentation clause is the pair
  `AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff` and
  `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`, read through
  `AlgebraicGeometry.Stack.forall_isSurjective_and_isSmooth_iff_hasRelativeProperty`.

The presentation clause is the only one whose quantifiers move. A presentation of the stack over
`S'` is a 1-morphism out of the category represented by an object `U'` of the site of `S'`, and
its mere existence forces `U'.hom` to factor through `g`, by the rigidity of relocalization
(`CategoryTheory.Over.exists_eq_map_of_comp_map`); the slice of the site of `S'` over `U'` is then
identified with the slice of the site of `S` over that factorization by
`AlgebraicGeometry.Stack.factorSliceFunctor`, and in the other direction a presentation by `U`
over `S` becomes one by `(Over.map g).obj U` over `S'` through
`AlgebraicGeometry.Stack.factorSliceInverse`. Neither identification is an equality of
categories, so the relative properties of Stacks 03YK have to be moved across it; that is
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalence_source`.

The universes are those of Stacks 04X5: the total category is taken with object universe one
above the scheme universe, which is where Construction B of Stacks 04WV — the one ingredient
whose universes are pinned — applies. -/
@[stacks 04X5 "algebraicity criterion"]
theorem isAlgebraicStack_changeBase_iff (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) :
    IsAlgebraicStack.{u, w} B S' hS' (changeBase B S S' hS hS' g 𝒳) ↔
      IsAlgebraicStack.{u, w} B S hS 𝒳 :=
  ⟨isAlgebraicStack_of_isAlgebraicStack_changeBase B S S' hS hS' g 𝒳,
    isAlgebraicStack_changeBase_of_isAlgebraicStack B S S' hS hS' g 𝒳⟩


/-- **Construction A on objects of the 2-category of algebraic stacks (Stacks 03YP).** An
algebraic stack over `S` is carried by Construction A to an algebraic stack over `S'`; the
algebraicity of the image is the forward direction of
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff`, which is what makes this map well
defined.

This is the object map of the correspondence Stacks 04X5 asks for. The correspondence itself is
assembled from it in a separate module: Construction B on objects together with the two round-trip
identities gives `AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv`, and the bijections
on 1-morphisms and 2-morphisms are
`AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv` and
`AlgebraicGeometry.Stack.algebraicStackConstructionHom₂Equiv`. -/
def changeBaseAlgebraicStack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w} B S' hS' :=
  ⟨changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val,
    (isAlgebraicStack_changeBase_iff B S S' hS hS' g 𝒳.val.val).2 𝒳.2⟩

/-- The category fibred in groupoids underlying Construction A of an algebraic stack is
Construction A of its underlying category fibred in groupoids. -/
@[simp]
lemma changeBaseAlgebraicStack_val (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).val =
      changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val :=
  rfl


end AlgebraicGeometry.Stack

end

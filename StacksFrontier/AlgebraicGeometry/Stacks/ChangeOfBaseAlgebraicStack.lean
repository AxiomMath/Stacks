module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# Construction A and algebraic stacks (Stacks 04X5 and 04X6)

Let `g : S ⟶ S'` be a morphism of a big fppf site. `AlgebraicGeometry.Stack.changeBase` views a
category over the big fppf site of `S` as a category over the big fppf site of `S'`; **Stacks
04X5** asserts that this identifies algebraic stacks over `S` with algebraic stacks over `S'`
equipped with a 1-morphism to the stack represented by `S`. This file proves the underlying
algebraicity statement in *both* directions: a category fibred in groupoids over the big fppf
site of `S` is an algebraic stack over `S` exactly when its image under Construction A is an
algebraic stack over `S'`. The forward direction is what makes **Stacks 04X6** — viewing an
algebraic stack over `S` as an algebraic stack over `S'` — a definition of an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_changeBase`: **Stacks 04X5**, the algebraic-stack
  clause of Stacks 026O transfers back along Construction A.
* `AlgebraicGeometry.Stack.isStack_changeBase` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_changeBase_of_isStack`: the stack clause transfers
  *forward* along Construction A, in each of the two renderings of Stacks 02ZJ.
* `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase`: **Stacks 04X5**, the algebraic-stack
  clause of Stacks 026O transfers *forward* along Construction A.
* `AlgebraicGeometry.Stack.changeBaseAlgebraicStacks`: **Stacks 04X6**, an algebraic stack over
  `S` viewed as an algebraic stack over `S'`.

## Implementation notes

**The reflecting direction.** Each of the four clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack` is already available in that direction in
`StacksFrontier/AlgebraicGeometry/Stacks/ChangeOfBase.lean`, except for the assembly done here:

* being fibred in groupoids is
  `AlgebraicGeometry.Stack.isFiberedInGroupoids_changeBase_iff`;
* the stack clause is the one direction of the stack-in-groupoids transfer that is proved,
  `AlgebraicGeometry.Stack.isStackInGroupoids_of_changeBase`, routed through the two
  implications of Stacks 02ZJ: the sieve-indexed condition of Stacks 026F gives the
  family-indexed one of Stacks 02ZI at the index universe `u + 1`
  (`CategoryTheory.Functor.IsStack.isStackInGroupoids`), the transfer applies there, and the
  family-indexed one gives back the sieve-indexed one over a base with fibre products
  (`CategoryTheory.Functor.isStack_of_isStackInGroupoids`). That round trip is why no
  statement at a general descent universe is needed of the transfer;
* the diagonal clause is
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`;
* the presentation clause is where the asymmetry of Construction A is absorbed. A presentation of
  `changeBase 𝒳` is a 1-morphism out of the category represented by an object `U'` of the big fppf
  site of `S'`, and the rigidity of relocalization
  (`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`) forces the structure morphism of
  `U'` to factor through `g`. The resulting object of the site of `S` is the presenting scheme, the
  two slices are identified by `AlgebraicGeometry.Stack.factorSliceFunctor`, and representability
  and the two relative properties are carried across by Stacks 0457 and 0459 in the source
  variable followed by
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`,
  `AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff` and
  `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`.

**The forward stack clause.** `AlgebraicGeometry.Stack.isStack_changeBase` now supplies the
implication that this file and `StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase` both recorded
as open, and it does *not* go the way those notes anticipated. The route described there — use
`CategoryTheory.Over.exists_factorization_of_mem_over` to factor the structure morphism of an
object carrying a descent datum through `g`, transfer the descent datum by
`CategoryTheory.Functor.Restriction.ofOverMap`,
`CategoryTheory.Functor.fibreHom_overMap_iff` and
`CategoryTheory.Functor.isRestrictionOf_overMap_iff`, then transport the covering family and its
restrictions back along the resulting identification of objects — is not needed, and no descent
datum is transported at all. Instead both sites are read as slices of the ambient category
`B.Schemes`, where `Over.map g ⋙ Over.forget (B.obj hS') = Over.forget (B.obj hS)` holds by
`rfl`, and the two implications of **Stacks 04WV** move the hypothesis down to the ambient site
and back up to the slice at `S'`. See the docstring of
`AlgebraicGeometry.Stack.isStack_changeBase`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04WV](https://stacks.math.columbia.edu/tag/04WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The representable presheaf of an object of a big fppf site is a sheaf.** The topology of a
big fppf site is subcanonical (`AlgebraicGeometry.BigFppfSite.subcanonical_topology`). -/
theorem isSheaf_yoneda_bigFppfSite (T : B.Schemes) :
    Presheaf.IsSheaf B.topology (yoneda.obj T) :=
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  (isSheaf_iff_isSheaf_of_type (J := B.topology) _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := B.topology) _)

/-- **The stack clause of Stacks 026F transfers along Construction A.** If a category over the big
fppf site of `S` is a stack for the fppf topology of `S`, then its image under Construction A is a
stack for the fppf topology of `S'`.

This is the implication that `StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase` leaves open, and
it is proved here without transporting any descent datum. The point is that the big fppf site of
`S` and the big fppf site of `S'` are *both* slices of the ambient category `B.Schemes` of the big
fppf site, and that Construction A is compatible with their two localization functors on the nose:

```text
  Over.map g ⋙ Over.forget (B.obj hS') = Over.forget (B.obj hS)
```

is true by `rfl`, since `Over.map g` changes only the structure morphism of an object and not its
underlying object. So the composite of `𝒳.p` with the localization functor of the site of `S` and
the composite of `(changeBase 𝒳).p` with that of the site of `S'` are *the same functor into the
ambient category*. The two implications of **Stacks 04WV** then do all the work: Construction A
for stacks (`CategoryTheory.Functor.isStack_comp_forget`) pushes the hypothesis down to the
ambient site, and Construction B (`CategoryTheory.Over.isStack_of_comp_forget_slice`) lifts it
back up to the slice at `S'`. Both need the representable presheaf of a slice object to be a
sheaf, which is subcanonicity of the ambient topology
(`AlgebraicGeometry.Stack.isSheaf_yoneda_bigFppfSite`).

**Universes.** `𝒳.obj` is pinned to `Type (u + 1)` with morphisms in `Type u`, which is where
Construction B is available: `CategoryTheory.Over.isStack_of_comp_forget_slice` asks for
`Type (max u₂ u₁)` with `Category.{u₁}` over a site in `Type u₂` with `Category.{u₁}`, and
`B.Schemes` is `Type (u + 1)` with `Category.{u}`. This is no restriction where the statement is
used: `AlgebraicGeometry.Stack.IsAlgebraicStack` is consumed at
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}` throughout. -/
theorem isStack_changeBase (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h : 𝒳.p.IsStack (BigFppfOver.topology B S hS)) :
    (changeBase B S S' hS hS' g 𝒳).p.IsStack (BigFppfOver.topology B S' hS') :=
  have h₁ : (𝒳.p ⋙ Over.forget (B.obj hS)).IsStack B.topology :=
    Functor.isStack_comp_forget 𝒳.p (isSheaf_yoneda_bigFppfSite B _) h
  Over.isStack_of_comp_forget_slice (B.obj hS') B.topology
    (isSheaf_yoneda_bigFppfSite B _) (𝒳.p ⋙ Over.map g) h₁

/-- **The stack-in-groupoids clause of Stacks 02ZI transfers along Construction A.** The
family-indexed rendering of the stack condition, at any descent universe, for the image of a
category fibred in groupoids under Construction A.

This is `AlgebraicGeometry.Stack.isStack_changeBase` followed by the implication of
**Stacks 02ZJ** from the sieve-indexed condition to the family-indexed one
(`CategoryTheory.Functor.IsStack.isStackInGroupoids`); it is the converse of
`AlgebraicGeometry.Stack.isStackInGroupoids_of_changeBase`.

The hypothesis is the *sieve-indexed* condition of Stacks 026F, which is what distinguishes this
from `AlgebraicGeometry.Stack.isStackInGroupoids_changeBase`: that statement transfers the
family-indexed condition at a fixed descent universe, whereas here the descent universe of the
conclusion is free because the hypothesis does not mention one. -/
theorem isStackInGroupoids_changeBase_of_isStack (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (h : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS)) :
    (changeBase B S S' hS hS' g 𝒳.val).p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S' hS') :=
  (isStack_changeBase B S S' hS hS' g 𝒳.val h).isStackInGroupoids.{w}
    ((isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳.val).2 𝒳.isFiberedInGroupoids)

/-- **The stack clause of Stacks 026F transfers back along Construction A.** A category over the
big fppf site of `S` which is fibred in groupoids and whose image under Construction A is a stack
for the fppf topology of `S'` is a stack for the fppf topology of `S`.

The two implications of Stacks 02ZJ turn the sieve-indexed condition into the family-indexed one
at the index universe `u + 1` and back; the transfer itself is
`AlgebraicGeometry.Stack.isStackInGroupoids_of_changeBase`. -/
theorem isStack_of_isStack_changeBase
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h : (changeBase B S S' hS hS' g 𝒳.val).p.IsStack (BigFppfOver.topology B S' hS')) :
    𝒳.val.p.IsStack (BigFppfOver.topology B S hS) := by
  have hfib : (changeBase B S S' hS hS' g 𝒳.val).p.IsFiberedInGroupoids :=
    (isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳.val).2 𝒳.isFiberedInGroupoids
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  exact Functor.isStack_of_isStackInGroupoids
    (isStackInGroupoids_of_changeBase B S S' hS hS' g 𝒳.val
      (h.isStackInGroupoids.{u + 1} hfib))

/-- **Stacks 04X5, the algebraic-stack clause in the direction Construction A reflects.** Let
`g : S ⟶ S'` be a morphism of a big fppf site and let `𝒳` be a category fibred in groupoids over
the big fppf site of `S`. If the category over the big fppf site of `S'` produced by Construction
A out of `𝒳` is an algebraic stack, then `𝒳` is an algebraic stack over `S`.

All four clauses of Stacks 026O are carried back: see the implementation notes. The descent
universe of the conclusion is free, because the sieve-indexed conjunct of the stack clause does
not depend on it. -/
@[stacks 04X5 "algebraicity transfers back along Construction A"]
theorem isAlgebraicStack_of_changeBase
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w'} B S' hS' (changeBase B S S' hS hS' g 𝒳.val)) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  classical
  have hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS) :=
    isStack_of_isStack_changeBase B S S' hS hS' g 𝒳
      (isStack_of_isAlgebraicStack B S' hS' h)
  obtain ⟨hfib', -, hdiag', U', f', hrep', hprop'⟩ := h
  -- the presenting object of the site of `S'` has its structure morphism factoring through `g`
  obtain ⟨h₀, hF, hh⟩ := Over.exists_eq_map_of_comp_map g U'.hom
    (Over.iteratedSliceBackward U' ⋙ f'.toFunctor ⋙ 𝒳.val.p)
    (by
      calc (Over.iteratedSliceBackward U' ⋙ f'.toFunctor ⋙ 𝒳.val.p) ⋙ Over.map g
          = Over.iteratedSliceBackward U' ⋙ f'.toFunctor ⋙ (𝒳.val.p ⋙ Over.map g) := rfl
        _ = Over.iteratedSliceBackward U' ⋙ Over.forget U' :=
              congrArg (fun F => Over.iteratedSliceBackward U' ⋙ F) f'.w
        _ = Over.map U'.hom := Over.iteratedSliceBackward_forget U')
  -- the presentation of `𝒳` it yields, through the identification of the two slices
  let a := factorSliceFunctor B S S' hS hS' g hh
  let f₀ : (schemeFibredCategory B S hS (Over.mk h₀)).val ⥤ᵇ 𝒳.val :=
    { toFunctor := Over.iteratedSliceForward (Over.mk h₀) ⋙
        (Over.iteratedSliceBackward U' ⋙ f'.toFunctor)
      w := by
        show Over.iteratedSliceForward (Over.mk h₀) ⋙
            (Over.iteratedSliceBackward U' ⋙ f'.toFunctor ⋙ 𝒳.val.p) =
          Over.forget (Over.mk h₀)
        rw [hF]
        exact Over.iteratedSliceForward_comp_map (Over.mk h₀) }
  have hcomp : BasedFunctor.comp a f' = changeBaseFunctor B S S' hS hS' g f₀ := rfl
  have hrepbig : IsRepresentableByAlgebraicSpaces B S' hS'
      (changeBaseFunctor B S S' hS hS' g f₀) := by
    rw [← hcomp]
    exact (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS'
      (𝒳' := changeBaseFiberedInGroupoids B S S' hS hS' g
        (schemeFibredCategory B S hS (Over.mk h₀)))
      (𝒳 := schemeFibredCategory B S' hS' U')
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      f' (BasedFunctor.comp a f') a (Iso.refl _)).1 hrep'
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f₀ :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f₀).1 hrepbig
  -- the two relative properties, carried along the equivalence of sources and then back along
  -- Construction A
  let 𝒳b := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳
  let Ub := changeBaseFiberedInGroupoids B S S' hS hS' g
    (schemeFibredCategory B S hS (Over.mk h₀))
  let f'h : schemeFibredCategory B S' hS' U' ⟶ 𝒳b := Bicategory.InducedBicategory.mkHom f'
  let fb : Ub ⟶ 𝒳b :=
    Bicategory.InducedBicategory.mkHom (changeBaseFunctor B S S' hS hS' g f₀)
  let bId : 𝒳b.val ⥤ᵇ 𝒳b.val := BasedFunctor.id 𝒳b.val
  have _ : Functor.IsEquivalence bId.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳b.val.obj))
  -- pin the universe of the locality instances, which the relative property does not determine
  have _ : (Space.surjectiveMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  have _ : (Space.smoothMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  have hp'surj : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.surjectiveMorphismProperty B S' hS') f'h hrep' :=
    fun T z hz G hG hE => (hprop' T z hz G hG hE).1
  have hp'smooth : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.smoothMorphismProperty B S' hS') f'h hrep' :=
    fun T z hz G hG hE => (hprop' T z hz G hG hE).2
  have hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f₀ : schemeFibredCategory B S hS (Over.mk h₀) ⟶ 𝒳)
      hrep :=
    (hasRelativeProperty_surjective_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS hS' g
        (Bicategory.InducedBicategory.mkHom f₀) hrep).1
      ((hasRelativeProperty_iff_of_equivalences B S' hS'
          (Space.surjectiveMorphismProperty B S' hS') fb f'h a bId (Iso.refl _) hrep').1
        hp'surj)
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f₀ : schemeFibredCategory B S hS (Over.mk h₀) ⟶ 𝒳)
      hrep :=
    (hasRelativeProperty_smooth_changeBaseHom_iff.{u, u, u + 1} B S S' hS hS' g
        (@AlgebraicGeometry.Smooth.{u}) (Bicategory.InducedBicategory.mkHom f₀) hrep).1
      ((hasRelativeProperty_iff_of_equivalences B S' hS'
          (Space.smoothMorphismProperty B S' hS') fb f'h a bId (Iso.refl _) hrep').1
        hp'smooth)
  exact ⟨𝒳.isFiberedInGroupoids, ⟨hstack, hstack.isStackInGroupoids.{w} 𝒳.isFiberedInGroupoids⟩,
    (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff B S S' hS hS' g 𝒳).1
      hdiag',
    Over.mk h₀, f₀, hrep,
    fun V y hy F hF he => ⟨hsurj V y hy F hF he, hsmooth V y hy F hF he⟩⟩

/-- **Stacks 04X5, the algebraic-stack clause in the direction Construction A produces.** Let
`g : S ⟶ S'` be a morphism of a big fppf site and let `𝒳` be a category fibred in groupoids over
the big fppf site of `S`. If `𝒳` is an algebraic stack over `S`, then the category over the big
fppf site of `S'` produced by Construction A out of `𝒳` is an algebraic stack over `S'`.

This is the converse of `AlgebraicGeometry.Stack.isAlgebraicStack_of_changeBase`, and it is the
statement that makes **Stacks 04X6** a definition of an algebraic stack rather than merely of a
category over the big fppf site of `S'`.

Three of the four clauses of Stacks 026O are the already-available biconditionals of
`StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase`, read in the forward direction: being fibred
in groupoids is `AlgebraicGeometry.Stack.isFiberedInGroupoids_changeBase_iff`, the stack clause is
`AlgebraicGeometry.Stack.isStack_changeBase` together with
`AlgebraicGeometry.Stack.isStackInGroupoids_changeBase_of_isStack`, and the diagonal clause is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`.
The descent universe of the conclusion is free, because the sieve-indexed conjunct of the stack
clause does not depend on it and the family-indexed one is derived from it at any universe.

The presentation clause is easier in this direction than in the reflecting one, and this is the
asymmetry of Construction A working in our favour. Reflection has to *discover* the presenting
object of the site of `S` inside a presentation by an object of the site of `S'`, which is what
forces `CategoryTheory.Over.exists_eq_map_of_comp_map` there. Here the presenting object is
simply pushed forward: a presentation of `𝒳` by `U` becomes a presentation of `changeBase 𝒳` by
`(CategoryTheory.Over.map g).obj U`, the two slices are identified by
`AlgebraicGeometry.Stack.factorSliceInverse` — which is exactly
`AlgebraicGeometry.Stack.factorSliceFunctor` taken in the direction that makes the comparison
isomorphism of Stacks 0457 the identity — and representability and the two relative properties
cross by `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`,
`AlgebraicGeometry.Stack.hasRelativeProperty_surjective_changeBaseHom_iff` and
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`, followed by Stacks 0457
and 0459 in the source variable along that identification. -/
@[stacks 04X5 "algebraicity transfers along Construction A"]
theorem isAlgebraicStack_changeBase
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicStack.{u, w'} B S' hS' (changeBase B S S' hS hS' g 𝒳.val) := by
  classical
  obtain ⟨hfib, ⟨hstack, -⟩, hdiag, U, f, hrep, hprop⟩ := h
  have hrepb : IsRepresentableByAlgebraicSpaces B S' hS'
      (changeBaseFunctor B S S' hS hS' g f) :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f).2 hrep
  have hrep' : IsRepresentableByAlgebraicSpaces B S' hS'
      (BasedFunctor.comp (factorSliceInverse B S S' hS hS' g U)
        (changeBaseFunctor B S S' hS hS' g f)) :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS'
      (𝒳' := schemeFibredCategory B S' hS' ((Over.map g).obj U))
      (𝒳 := changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS U))
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g
        (CatFiberedInGroupoids.mk 𝒳.val hfib))
      (changeBaseFunctor B S S' hS hS' g f) _
      (factorSliceInverse B S S' hS hS' g U) (Iso.refl _)).1 hrepb
  -- pin the universe of the locality instances, which the relative property does not determine
  have _ : (Space.surjectiveMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  have _ : (Space.smoothMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  let 𝒳b := changeBaseFiberedInGroupoids B S S' hS hS' g (CatFiberedInGroupoids.mk 𝒳.val hfib)
  let a := factorSliceInverse B S S' hS hS' g U
  let bId : 𝒳b.val ⥤ᵇ 𝒳b.val := BasedFunctor.id 𝒳b.val
  have _ : Functor.IsEquivalence bId.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳b.val.obj))
  let fh : schemeFibredCategory B S hS U ⟶ CatFiberedInGroupoids.mk 𝒳.val hfib :=
    Bicategory.InducedBicategory.mkHom f
  let fprime : schemeFibredCategory B S' hS' ((Over.map g).obj U) ⟶ 𝒳b :=
    Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp a (changeBaseFunctor B S S' hS hS' g f))
  have hsurj : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.surjectiveMorphismProperty B S' hS') fprime hrep' :=
    (hasRelativeProperty_iff_of_equivalences B S' hS'
      (Space.surjectiveMorphismProperty B S' hS') fprime
      (changeBaseHom B S S' hS hS' g fh) a bId (Iso.refl _) hrepb).1
      ((hasRelativeProperty_surjective_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS hS' g
          fh hrep).2 (fun T z hz G hG hE => (hprop T z hz G hG hE).1))
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.smoothMorphismProperty B S' hS') fprime hrep' :=
    (hasRelativeProperty_iff_of_equivalences B S' hS'
      (Space.smoothMorphismProperty B S' hS') fprime
      (changeBaseHom B S S' hS hS' g fh) a bId (Iso.refl _) hrepb).1
      ((hasRelativeProperty_smooth_changeBaseHom_iff.{u, u, u + 1} B S S' hS hS' g
          (@AlgebraicGeometry.Smooth.{u}) fh hrep).2
        (fun T z hz G hG hE => (hprop T z hz G hG hE).2))
  exact ⟨(isFiberedInGroupoids_changeBase_iff B S S' hS hS' g 𝒳.val).2 hfib,
    ⟨isStack_changeBase B S S' hS hS' g 𝒳.val hstack,
     isStackInGroupoids_changeBase_of_isStack B S S' hS hS' g 𝒳 hstack⟩,
    (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff
      B S S' hS hS' g 𝒳).2 hdiag,
    (Over.map g).obj U, _, hrep',
    fun V y hy F hF he => ⟨hsurj V y hy F hF he, hsmooth V y hy F hF he⟩⟩

/-- **Stacks 04X6.** An algebraic stack `𝒳` over `S`, *viewed as an algebraic stack over `S'`*
along a morphism `g : S ⟶ S'` of the big fppf site: the algebraic stack over `S'` obtained by
applying Construction A of **Stacks 04X5** to `𝒳`.

The underlying category and its structure functor are `AlgebraicGeometry.Stack.changeBase`, which
composes the structure functor of `𝒳` with `CategoryTheory.Over.map g`; the content of the
definition is that the result is again an algebraic stack, which is
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase`. -/
@[stacks 04X6]
def changeBaseAlgebraicStacks (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w'} B S' hS' :=
  ⟨changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val,
    isAlgebraicStack_changeBase B S S' hS hS' g 𝒳.val 𝒳.property⟩

/-- The underlying category fibred in groupoids of the base change of an algebraic stack is the
base change of its underlying category fibred in groupoids. -/
@[simp]
lemma changeBaseAlgebraicStacks_val (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (changeBaseAlgebraicStacks.{u, w, w'} B S S' hS hS' g 𝒳).val =
      changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val :=
  rfl

end AlgebraicGeometry.Stack

end

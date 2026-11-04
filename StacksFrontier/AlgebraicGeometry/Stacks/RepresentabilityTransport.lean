module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Transporting representability by algebraic spaces along an equivalence over the site

`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` (Stacks 04SV) and
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` (Stacks 02ZW) are both stated as the
existence of a `StacksRepresentableCFG.EquivalenceOver` into the category attached to the sheaf
of points of an algebraic space. Every representability argument therefore needs to move such a
witness along a comparison of the categories being compared, and this file collects the ways of
doing that.

For `IsRepresentableByAlgebraicSpace` the transport is nothing but composition of equivalences
over the site, `StacksRepresentableCFG.EquivalenceOver.trans`.

For `IsRepresentableByAlgebraicSpaces` there are two regimes, and which one applies depends on
whether the base of the quantification moves:

* if the target `𝒴` and the scheme-valued point `y` are unchanged, so that only the 2-fibre
  product `(Sch/U)_{fppf} ×_𝒴 𝒳` is replaced, the transport is again pointwise composition of
  equivalences over the site of `U`: that is
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst`. It
  needs no hypothesis beyond the equivalences themselves — in particular neither category has
  to be fibred in groupoids — and it is what a comparison of 2-fibre products such as
  `CategoryTheory.TwoFibreProductOver.mapSndEquivalenceOver` or
  `CategoryTheory.TwoFibreProductOver.cancelMiddleEquivalenceOver` feeds directly.
* if the source or the target of the 1-morphism itself moves, the quantification over
  scheme-valued points of the target has to be matched up, and the transport is the content of
  Stacks 0457,
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`, which handles
  a 2-commutative square with both horizontal morphisms equivalences. The two one-sided cases
  below specialise it by taking the other horizontal morphism to be the identity.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_equivalenceOver` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_of_equivalenceOver`: transport of
  **Stacks 04SV** along an equivalence over the site.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst`, its
  `Nonempty` form
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`
  and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_forall_equivalenceOver_fst`:
  transport of **Stacks 02ZW** along a family of equivalences of the first projections.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_target`:
  transport of **Stacks 02ZW** in the source, resp. in the target, of the 1-morphism.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_source` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_target`: the
  same two, with the equivalence supplied as a `StacksRepresentableCFG.EquivalenceOver` rather
  than as a bare equivalence of the underlying categories.

## Implementation notes

The universes are those of the two predicates themselves, with no relation imposed between the
object and morphism universes of the various total categories: `Stacks 04SV` fixes its argument
at `CategoryTheory.CatFiberedInGroupoids.{u, v, u + 1, w}` with `v` and `w` free, and
`Stacks 02ZW` takes `CategoryTheory.BasedCategory.{v, w}`s with independent `v`, `w` for source
and target. The pointwise lemma for `Stacks 02ZW` is accordingly stated for three
`BasedCategory`s at three independent pairs of universes, and the two one-sided lemmas inherit
`CategoryTheory.CatFiberedInGroupoids` at three independent pairs from Stacks 0457. No 2-fibre
product apex is constructed here, which is why the universes can stay free: the 2-fibre products
appearing in the statements are the ones `Stacks 02ZW` already quantifies over.

The one-sided lemmas take the comparison 2-cell in the shape Stacks 0457 wants, with the
identity horizontal morphism already cancelled — `BasedFunctor.comp f' (BasedFunctor.id _)` and
`BasedFunctor.comp (BasedFunctor.id _) f` are definitionally `f'` and `f`.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ v₃ w₁ w₂ w₃

section Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A category fibred in groupoids equivalent over the big fppf site of `S` to one that is
represented by an algebraic space over `S` is itself represented by an algebraic space over `S`:
compose the given equivalence with the representing one. -/
theorem isRepresentableByAlgebraicSpace_of_equivalenceOver
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒳' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳'.val.p 𝒳.val.p)
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳' := by
  obtain ⟨F, hF, ⟨E⟩⟩ := h
  exact ⟨F, hF, ⟨e.trans E⟩⟩

/-- Being represented by an algebraic space is invariant under equivalence over the big fppf
site of `S`. The two directions are
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_equivalenceOver` applied to the
given equivalence and to its inverse. -/
theorem isRepresentableByAlgebraicSpace_iff_of_equivalenceOver
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒳' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳'.val.p 𝒳.val.p) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 ↔ IsRepresentableByAlgebraicSpace B S hS 𝒳' :=
  ⟨isRepresentableByAlgebraicSpace_of_equivalenceOver e,
    isRepresentableByAlgebraicSpace_of_equivalenceOver e.symm⟩

end Space

section Pointwise

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒳' : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₃, w₃} (BigFppfOver B S hS)}

/-- **Transport of Stacks 02ZW along a family of equivalences of the first projections.** If,
for every scheme `U` over `S` and every scheme-valued point `y` of `𝒴` over `U`, the first
projection of `(Sch/U)_{fppf} ×_{y, 𝒴, f'} 𝒳'` is equivalent over the big fppf site of `U` to
that of `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`, then `f'` is representable by algebraic spaces as soon
as `f` is.

This is the cheap half of the transport: the target `𝒴` and the point `y` do not move, so the
quantification matches up on the nose and the conclusion is composition of equivalences over
the site of `U`. Neither source has to be fibred in groupoids. -/
theorem isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst
    {f : 𝒳 ⥤ᵇ 𝒴} {f' : 𝒳' ⥤ᵇ 𝒴}
    (e : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj), y ⋙ 𝒴.p = Over.map U.hom →
      StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.p 𝒴.p y f'.toFunctor)
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor))
    (h : IsRepresentableByAlgebraicSpaces B S hS f) :
    IsRepresentableByAlgebraicSpaces B S hS f' := by
  dsimp only [IsRepresentableByAlgebraicSpaces] at h ⊢
  intro U y hy
  obtain ⟨F, hF, ⟨E⟩⟩ := h U y hy
  exact ⟨F, hF, ⟨(e U y hy).trans E⟩⟩

/-- `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst`
with the equivalences supplied only up to `Nonempty`, which is the shape they come in from
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` and from comparison theorems such as
`CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia`. The `Nonempty` sits
inside the quantifier, so it cannot be stripped by the caller without a choice; the conclusion
is a proposition, so it can be stripped here. -/
theorem isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst
    {f : 𝒳 ⥤ᵇ 𝒴} {f' : 𝒳' ⥤ᵇ 𝒴}
    (e : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj), y ⋙ 𝒴.p = Over.map U.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.p 𝒴.p y f'.toFunctor)
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor)))
    (h : IsRepresentableByAlgebraicSpaces B S hS f) :
    IsRepresentableByAlgebraicSpaces B S hS f' := by
  exact isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst
    (fun U y hy => (e U y hy).some) h

/-- The biconditional form of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst`: a
family of equivalences of the first projections, read in both directions. -/
theorem isRepresentableByAlgebraicSpaces_iff_of_forall_equivalenceOver_fst
    {f : 𝒳 ⥤ᵇ 𝒴} {f' : 𝒳' ⥤ᵇ 𝒴}
    (e : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj), y ⋙ 𝒴.p = Over.map U.hom →
      StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.p 𝒴.p y f'.toFunctor)
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor)) :
    IsRepresentableByAlgebraicSpaces B S hS f ↔ IsRepresentableByAlgebraicSpaces B S hS f' :=
  ⟨isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst e,
    isRepresentableByAlgebraicSpaces_of_forall_equivalenceOver_fst
      (fun U y hy => (e U y hy).symm)⟩

end Pointwise

section OneSided

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport of Stacks 02ZW in the source.** An equivalence `a` of the sources over the big
fppf site of `S`, identifying `f'` with `a ⋙ f`, carries representability by algebraic spaces
from `f` to `f'` and back. This is Stacks 0457 with the horizontal morphism of targets taken to
be the identity. -/
theorem isRepresentableByAlgebraicSpaces_iff_of_equivalence_source
    {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (f' : 𝒳'.val ⥤ᵇ 𝒴.val) (a : 𝒳'.val ⥤ᵇ 𝒳.val)
    (α : BasedFunctor.comp a f ≅ f')
    [Functor.IsEquivalence a.toFunctor] :
    IsRepresentableByAlgebraicSpaces B S hS f ↔ IsRepresentableByAlgebraicSpaces B S hS f' := by
  have : Functor.IsEquivalence (BasedFunctor.id 𝒴.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.obj))
  exact isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f' f a
    (BasedFunctor.id 𝒴.val) α

/-- **Transport of Stacks 02ZW in the target.** An equivalence `b` of the targets over the big
fppf site of `S`, identifying `f` with `f' ⋙ b`, carries representability by algebraic spaces
from `f` to `f'` and back. This is Stacks 0457 with the horizontal morphism of sources taken to
be the identity; unlike the source case it genuinely needs 0457, because changing the target
changes the family of scheme-valued points the predicate quantifies over. -/
theorem isRepresentableByAlgebraicSpaces_iff_of_equivalence_target
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (f' : 𝒳.val ⥤ᵇ 𝒴'.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : f ≅ BasedFunctor.comp f' b)
    [Functor.IsEquivalence b.toFunctor] :
    IsRepresentableByAlgebraicSpaces B S hS f ↔ IsRepresentableByAlgebraicSpaces B S hS f' := by
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  exact isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f' f
    (BasedFunctor.id 𝒳.val) b α

/-- `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source` with the
equivalence of sources supplied as a `StacksRepresentableCFG.EquivalenceOver`, whose forward
1-morphism is the 1-morphism of the square and whose underlying functor is an equivalence by
`StacksRepresentableCFG.EquivalenceOver.isEquivalence_hom_functor`. -/
theorem isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_source
    {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (f' : 𝒳'.val ⥤ᵇ 𝒴.val)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳'.val.p 𝒳.val.p)
    (α : BasedFunctor.comp ⟨e.hom.functor, e.hom.w⟩ f ≅ f') :
    IsRepresentableByAlgebraicSpaces B S hS f ↔ IsRepresentableByAlgebraicSpaces B S hS f' := by
  have := e.isEquivalence_hom_functor
  exact isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS f f' _ α

/-- `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_target` with the
equivalence of targets supplied as a `StacksRepresentableCFG.EquivalenceOver`. -/
theorem isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_target
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (f' : 𝒳.val ⥤ᵇ 𝒴'.val)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴'.val.p 𝒴.val.p)
    (α : f ≅ BasedFunctor.comp f' ⟨e.hom.functor, e.hom.w⟩) :
    IsRepresentableByAlgebraicSpaces B S hS f ↔ IsRepresentableByAlgebraicSpaces B S hS f' := by
  have := e.isEquivalence_hom_functor
  exact isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS f f' _ α

end OneSided

end AlgebraicGeometry.Stack

end

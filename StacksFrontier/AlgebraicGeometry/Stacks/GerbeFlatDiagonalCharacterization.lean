module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections

/-!
# Gerbes are the morphisms whose diagonal is flat (Stacks 0CPS)

**Stacks 0CPS** is the equivalence, for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`,
of

1. `f` makes `𝒳` a gerbe over `𝒴` (**Stacks 06QC**), and
2. both `f` and its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` are surjective, flat and locally of
   finite presentation.

## The two implications

(2) `⟹` (1) is proved here. Both clauses of
the gerbe condition — Stacks 06P1 (2)(a) and (2)(b) — are instances of **Stacks 06QA**
(`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`): a surjective, flat, locally finitely
presented 1-morphism admits, over an fppf covering of any object of the site, a lift of any
object of a fibre of its target.

For clause (2)(a) this is Stacks 06QA for `f` itself. For clause (2)(b) it is Stacks 06QA for
`Δ_f`, read at the object of `𝒳 ×_𝒴 𝒳` determined by the datum of the clause. A vertical
morphism `b : f x ⟶ f x'` of `𝒴` is an isomorphism, the fibres of a category fibred in
groupoids being groupoids, so the triple `(x, x', b)` is an object of the 2-fibre product of
**Stacks 04T2** over the object of the site that `b` lies over. A morphism to it out of
`Δ_f z = (z, z, id)` is a pair of morphisms `(a : z ⟶ x, b' : z ⟶ x')` lying over one morphism
of the site with `f a ≫ b = f b'`; so the lift produced by Stacks 06QA along a member `k` of
the covering is exactly the datum clause (2)(b) asks for along `k`, with the vertical morphism
taken to be the identity of `z`.

(1) `⟹` (2) is the assembly of **Stacks 06QI** and **Stacks 0CPR**, part (2), as in the source.
Surjectivity of `f` is `AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver` and surjectivity
of `Δ_f` is `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_relativeDiagonal_of_isGerbeOver`;
flatness and local finite presentation of both are proved in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness`, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`
and its sibling `isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`.

## Main results

All of these live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isGerbeOver_of_isSurjective_isFlat_isLfp`: the implication (2) `⟹` (1).
* `isSurjective_isFlat_isLfp_of_isGerbeOver`: the implication (1) `⟹` (2).
* `isGerbeOver_iff_isSurjective_isFlat_isLfp`: **Stacks 0CPS**, the equivalence.

## Implementation notes

The source proves (2) `⟹` (1) by descending along a surjective, flat, locally finitely
presented base change until the target is a scheme, applying **Stacks 06QJ** to the inertia and
then identifying the algebraic space of isomorphism classes of **Stacks 06QD** with the target.
The route taken here reads both clauses of the gerbe condition directly off Stacks 06QA, which
is the lemma the source itself uses for the surjectivity half of the identification step, and
needs neither the reduction to a scheme nor the inertia.

The object of `𝒳 ×_𝒴 𝒳` attached to the datum of clause (2)(b) is the quadruple of
`CategoryTheory.TwoFibreProductOver`, whose comparison isomorphism is required to be vertical;
that is exactly the hypothesis on `b`, so the only work is to turn `b` into an isomorphism,
which is `CategoryTheory.Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id`. The two
components of the lift are read off as morphisms of the fibres by composing with the two
projections, which are strictly over the site
(`CategoryTheory.TwoFibreProductOver.fst_comp_eq` and
`CategoryTheory.TwoFibreProductOver.snd_comp_eq`), so
`CategoryTheory.Functor.isHomLift_comp_iff` transfers the lifting datum from the 2-fibre product
to `𝒳`.

The gerbe condition is stated with `f ⋙ 𝒴.p` as the structure functor of `𝒳` rather than with
`𝒳.p`, as the implementation notes of `StacksFrontier.CategoryTheory.Sites.Gerbe.Basic` explain;
the two agree by the `w` field of `f`, which is
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`, and rewriting with it moves each
lifting statement between the two.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QD](https://stacks.math.columbia.edu/tag/06QD)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
* [Stacks Project, Tag 0CPS](https://stacks.math.columbia.edu/tag/0CPS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CPS, the implication (2) `⟹` (1).** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` and its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` are both surjective, flat and
locally of finite presentation, then `f` makes `𝒳` a gerbe over `𝒴`.

Both local conditions of Stacks 06P1 (2) are **Stacks 06QA**. For (2)(a) it is applied to `f`.
For (2)(b) it is applied to `Δ_f` at the object `(x, x', b)` of `𝒳 ×_𝒴 𝒳`, whose comparison
isomorphism is the given vertical morphism; a lift of that object along a member of the fppf
covering is a pair of morphisms out of a single object `z` of `𝒳` whose `f`-images differ by
`b`, which is the datum (2)(b) asks for, with the identity of `z` as its vertical morphism. -/
theorem isGerbeOver_of_isSurjective_isFlat_isLfp
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hfsurj : Stack.IsSurjective B S hS f) (hfflat : IsFlat B S hS f)
    (hflfp : IsLocallyOfFinitePresentation B S hS f)
    (hdsurj : Stack.IsSurjective B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f))
    (hdflat : IsFlat B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f))
    (hdlfp : IsLocallyOfFinitePresentation B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS f)) :
    IsGerbeOver B S hS f := by
  refine ⟨𝒴.val.isFiberedInGroupoids, ?_, ?_, ?_⟩
  · rw [CatFiberedInGroupoids.homFunctor_comp_p f.hom]
    exact 𝒳.val.isFiberedInGroupoids
  · -- Stacks 06P1 (2)(a) is Stacks 06QA for `f`.
    intro U y hy
    obtain ⟨R, hR, hlift⟩ :=
      Stack.exists_fppfCovering_fibre_lift B S hS f hfsurj hfflat hflfp U ⟨y, hy⟩
    exact ⟨R, hR, fun _ _ hk => hlift hk⟩
  · -- Stacks 06P1 (2)(b) is Stacks 06QA for `Δ_f`.
    intro U x x' b hb
    have hbiso : IsIso b :=
      Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id 𝒴.val.isFiberedInGroupoids b hb
    have hx : 𝒳.val.val.p.obj x = U :=
      (BasedFunctor.w_obj f.hom.hom x).symm.trans (IsHomLift.domain_eq 𝒴.val.val.p (𝟙 U) b)
    have hx' : 𝒳.val.val.p.obj x' = U :=
      (BasedFunctor.w_obj f.hom.hom x').symm.trans (IsHomLift.codomain_eq 𝒴.val.val.p (𝟙 U) b)
    -- The object of `𝒳 ×_𝒴 𝒳` determined by `(x, x', b)`.
    let P : TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor f.hom) :=
      { base := U, x := x, y := x', hx := hx, hy := hx', iso := asIso b, vertical := hb }
    obtain ⟨R, hR, hlift⟩ := Stack.exists_fppfCovering_fibre_lift B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS f) hdsurj hdflat hdlfp U ⟨P, rfl⟩
    refine ⟨R, hR, fun V k hk => ?_⟩
    obtain ⟨z, α, hα⟩ := hlift hk
    -- The two components of the lift, read off through the projections of the 2-fibre product.
    have hαa : 𝒳.val.val.p.IsHomLift k α.a := by
      refine (Functor.isHomLift_comp_iff (TwoFibreProductOver.fst _ _ _ _ _) _ k α).1 ?_
      rw [TwoFibreProductOver.fst_comp_eq]
      exact hα
    have hαb : 𝒳.val.val.p.IsHomLift k α.b := by
      refine (Functor.isHomLift_comp_iff (TwoFibreProductOver.snd _ _ _ _ _) _ k α).1 ?_
      rw [TwoFibreProductOver.snd_comp_eq]
      exact hα
    have hzV : 𝒳.val.val.p.obj z = V :=
      IsHomLift.domain_eq (Stack.twoFibreProductAlgebraicStack B S hS f f).val.val.p k α
    have hsq : (CatFiberedInGroupoids.homFunctor f.hom).map (𝟙 z) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map α.b =
        (CatFiberedInGroupoids.homFunctor f.hom).map α.a ≫ b := by
      rw [CategoryTheory.Functor.map_id]
      exact α.w.symm
    refine ⟨z, z, α.a, α.b, 𝟙 z, ?_, ?_, ?_, hsq⟩
    all_goals rw [CatFiberedInGroupoids.homFunctor_comp_p f.hom]
    exacts [hαa, hαb, IsHomLift.id hzV]

/-- **Stacks 0CPS, the implication (1) `⟹` (2).** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` makes `𝒳` a gerbe over `𝒴`, then `f` and its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` are surjective, flat and locally of finite presentation.

This is **Stacks 06QI** for `f` and **Stacks 0CPR**, part (2), for `Δ_f`:
`Stack.isSurjective_of_isGerbeOver` and `isSurjective_relativeDiagonal_of_isGerbeOver` for
surjectivity, `isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver` and
`isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal` for the other two properties. -/
theorem isSurjective_isFlat_isLfp_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) :
    (Stack.IsSurjective B S hS f ∧ IsFlat B S hS f ∧
        IsLocallyOfFinitePresentation B S hS f) ∧
      (Stack.IsSurjective B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
        IsFlat B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
        IsLocallyOfFinitePresentation B S hS
          (Stack.relativeDiagonalAlgebraicStacks B S hS f)) :=
  ⟨⟨Stack.isSurjective_of_isGerbeOver B S hS f hf,
      isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf⟩,
    isSurjective_relativeDiagonal_of_isGerbeOver B S hS f hf,
      isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf⟩

/-- **Stacks 0CPS.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Then `𝒳` is
a gerbe over `𝒴` if and only if `f` and its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` are both
surjective, flat and locally of finite presentation.

The implication from the gerbe condition is **Stacks 06QI** and **Stacks 0CPR**, part (2)
(`isSurjective_isFlat_isLfp_of_isGerbeOver`); the converse reads both clauses of the gerbe
condition off **Stacks 06QA** applied to `f` and to `Δ_f`
(`isGerbeOver_of_isSurjective_isFlat_isLfp`). -/
@[stacks 0CPS]
theorem isGerbeOver_iff_isSurjective_isFlat_isLfp
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsGerbeOver B S hS f ↔
      (Stack.IsSurjective B S hS f ∧ IsFlat B S hS f ∧
          IsLocallyOfFinitePresentation B S hS f) ∧
        (Stack.IsSurjective B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
          IsFlat B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
          IsLocallyOfFinitePresentation B S hS
            (Stack.relativeDiagonalAlgebraicStacks B S hS f)) :=
  ⟨isSurjective_isFlat_isLfp_of_isGerbeOver B S hS f,
    fun h => isGerbeOver_of_isSurjective_isFlat_isLfp B S hS f h.1.1 h.1.2.1 h.1.2.2
      h.2.1 h.2.2.1 h.2.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end

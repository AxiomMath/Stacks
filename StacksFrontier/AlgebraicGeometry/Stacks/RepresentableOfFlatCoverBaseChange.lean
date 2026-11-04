module

public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp

/-!
# Representability can be checked after a flat cover (Stacks 04ZP, (2) ⟹ (1))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `𝒲 ⟶ 𝒴` be a surjective,
flat, locally finitely presented 1-morphism whose source is an algebraic space. Stacks 04ZP says
that `f` is representable by algebraic spaces as soon as `𝒲 ×_𝒴 𝒳` is an algebraic space. The
converse implication is `Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`
(Stacks 0300).

## Main results

* `locallyEssSurjOnFibers_of_representable_isSurjective_isFlat_isLocallyOfFinitePresentation`:
  a surjective, flat, locally finitely presented 1-morphism of algebraic stacks which is
  representable by algebraic spaces is locally essentially surjective on fibres in the form
  Stacks 06DV asks for.
* `isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_pt`: if some 2-fibre
  product of `f` with a surjective, flat, locally finitely presented 1-morphism from an algebraic
  space is an algebraic space, then `f` is representable by algebraic spaces.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A surjective, flat, locally finitely presented 1-morphism of algebraic stacks which is
representable by algebraic spaces is locally essentially surjective on fibres
(`CategoryTheory.Functor.LocallyEssSurjOnFibers`, as in Stacks 06DV): every object of a fibre of
the target becomes, along the members of a covering sieve, isomorphic to the chosen pullback of
an image of an object of the source. -/
theorem locallyEssSurjOnFibers_of_representable_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hSurj : IsSurjective B S hS g) (hFlat : AlgebraicStacks.IsFlat B S hS g)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g) :
    Functor.LocallyEssSurjOnFibers 𝒴.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom) (BigFppfOver.topology B S hS) := by
  have : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  intro U y
  obtain ⟨R, hR, hloc⟩ :=
    localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hg hSurj hFlat
      hLfp U y
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hloc hk
  have hz : 𝒵.val.val.p.obj z = V :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p g.hom) z).symm.trans
      (IsHomLift.domain_eq 𝒴.val.val.p k φ)
  exact ⟨⟨z, hz⟩, ⟨Functor.fiberIsoPullbackFiber 𝒴.val.val.p y k _ φ
    (𝒴.val.isFiberedInGroupoids.isStronglyCartesian_homLift k φ)⟩⟩

/-- The projection to the first factor of the canonical 2-fibre product of a cospan of algebraic
stacks is faithful as soon as *some* 2-fibre product of the cospan is an algebraic space. -/
theorem faithful_twoFibreProductOver_fst_of_isRepresentableByAlgebraicSpace
    {𝒳 𝒴 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt.val) :
    (TwoFibreProductOver.fst 𝒲.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor f.hom)).Faithful := by
  have hQfst : Q.fst.hom.hom.toFunctor.Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS Q.fst
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒲.property hQpt Q.fst.hom)
  let a := Bicategory.twoFibreProductPreHom hQ (twoFibreProductSquareAlgebraicStacks B S hS g f)
  have ha : a.hom.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hQ a
  have hcomp : (a.hom ≫ Q.fst).hom.hom.toFunctor.Faithful :=
    @Functor.Faithful.comp _ _ _ _ _ _ a.hom.hom.hom.toFunctor Q.fst.hom.hom.toFunctor
      ha.faithful hQfst
  exact @Functor.Faithful.of_iso _ _ _ _ _ _ hcomp
    (CatFiberedInGroupoids.underlyingIso (Bicategory.InducedBicategory.isoHom a.isoFst)).symm

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `g : 𝒲 ⟶ 𝒴` be
surjective, flat and locally of finite presentation with `𝒲` an algebraic space, and suppose a
2-fibre product `𝒲 ×_𝒴 𝒳` of the cospan `(g, f)` is an algebraic space. Then `f` is
representable by algebraic spaces. -/
@[stacks 04ZP "the implication (2) ⟹ (1)"]
theorem isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_pt
    {𝒳 𝒴 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲.val)
    (hSurj : IsSurjective B S hS g) (hFlat : AlgebraicStacks.IsFlat B S hS g)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt.val) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom := by
  refine isRepresentableByAlgebraicSpaces_of_faithful B S hS f ?_
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property h𝒲 g.hom
  exact Functor.faithful_of_faithful_fst (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids 𝒳.property.2.1.1
    (locallyEssSurjOnFibers_of_representable_isSurjective_isFlat_isLocallyOfFinitePresentation
      B S hS g hg hSurj hFlat hLfp)
    (faithful_twoFibreProductOver_fst_of_isRepresentableByAlgebraicSpace B S hS f g Q hQ hQpt)

end AlgebraicGeometry.Stack.AlgebraicStacks

end

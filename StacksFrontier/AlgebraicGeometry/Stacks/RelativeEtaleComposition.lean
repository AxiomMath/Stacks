module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# Composing relative étaleness (Stacks 045B at étaleness)

Facts about `AlgebraicGeometry.Stack.IsRelativelyEtale` that the étale analogue of the
universal smooth-diagram construction of **Stacks 06FM** needs: that relative étaleness is
stable under composition — **Stacks 045B** at étaleness — that it survives composition with a
1-morphism whose underlying functor is an equivalence, and that the backward 1-morphism of a
representing equivalence (`AlgebraicGeometry.Stack.equivalenceOverInvMap`) is relatively étale.

## Main results

* `AlgebraicGeometry.Space.etaleMorphisms_isLocalAtTarget_fppf`: **Stacks 042B** read on the
  fppf precoverage of Stacks 03YH.
* `AlgebraicGeometry.Stack.isRelativelyEtale_comp`: **Stacks 045B** at étaleness — a composite
  of relatively étale 1-morphisms is relatively étale.
* `AlgebraicGeometry.Stack.isRelativelyEtale_comp_of_isEquivalence` and
  `AlgebraicGeometry.Stack.isRelativelyEtale_of_isEquivalence_comp`: relative étaleness is
  preserved by post- and precomposition with a 1-morphism whose underlying functor is an
  equivalence.
* `AlgebraicGeometry.Stack.isRelativelyEtale_equivalenceOverInvMap`: the backward 1-morphism of
  a representing equivalence is relatively étale.

## Implementation notes

The unrestricted composition statement is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_comp`: `AlgebraicGeometry.Stack.HasRelativeProperty`
cannot appear in the *statement* of relative étaleness, because it carries
`[P.IsStableUnderBaseChange]` and
`[P.IsLocalAtTarget (AlgebraicGeometry.Space.Topology.fppf.precoverage B S hS)]` as instance
arguments and `AlgebraicGeometry.Stack.IsRelativelyEtale` is written longhand for that reason;
but the longhand is that definition's body at
`AlgebraicGeometry.Space.etaleMorphisms`, so `AlgebraicGeometry.Stack.hasRelativeProperty_comp`
(**Stacks 045B**) does apply once the two instances are supplied. Base-change stability is
**Stacks 03FU**, `AlgebraicGeometry.Space.etaleMorphisms_isStableUnderBaseChange`, and locality
at the target for the fppf precoverage is `etaleMorphisms_isLocalAtTarget_fppf` below: étaleness
of morphisms of algebraic spaces is local at the target for the *fpqc* precoverage by
**Stacks 042B**, `AlgebraicGeometry.Space.isEtale_isLocalAtTarget_fpqc`, which is stronger
because the fppf precoverage is contained in the fpqc one
(`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`). Stability under composition is
**Stacks 03FT**, `AlgebraicGeometry.Space.etaleMorphisms_isMultiplicative`.

The two statements restricted to an equivalence predate the unrestricted one and are kept: each
is a one-step transport, and neither asks for the three instances. They go through
`AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences` (**Stacks 0457** at étaleness), for
which the equivalence is the horizontal 1-morphism of a 2-commutative square whose other
horizontal 1-morphism is the identity. They are the étale readings of
`AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence` and
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isEquivalence_comp`, with the same proofs; the
quasi-inverse over the site that the postcomposition case needs is Stacks 003Z (2),
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`.

`isRelativelyEtale_equivalenceOverInvMap` is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap`: the bridge of **Stacks 04XB**
at étaleness (`AlgebraicGeometry.Stack.isRelativelyEtale_iff_isEtale_representingMap`) reduces it
to étaleness of the induced morphism of representing presheaves, and that morphism is the
identity of `F` by `AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`.

Nothing here carries a `@[stacks]` attribute. Stacks 045B is already registered on
`AlgebraicGeometry.Stack.hasRelativeProperty_comp`, of which `isRelativelyEtale_comp` is one
instantiation; Stacks 042B is already registered on
`AlgebraicGeometry.Space.isEtale_isLocalAtTarget_fpqc`, of which the locality instance below is
the transport along a comparison of precoverages; and Stacks 0457 is already registered on
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`, whose covering set
`AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences` belongs to.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

/-- **Stacks 042B at the fppf precoverage.** Étaleness of morphisms of algebraic spaces over `S`
is local at the target for the fppf topology of **Stacks 03YH**. The fpqc form is
`AlgebraicGeometry.Space.isEtale_isLocalAtTarget_fpqc`, and the two are compared by
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. This is the form in which the
relative properties of **Stacks 03YK** ask for it. -/
instance etaleMorphisms_isLocalAtTarget_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (etaleMorphisms B S hS).IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045B at étaleness.** A composite of two 1-morphisms of categories fibred in
groupoids over the big fppf site of `S` which are étale in the sense of **Stacks 04XB** is
étale.

Representability of the composite is **Stacks 03Y1** and the relative property of **Stacks
03YK** composes by **Stacks 045B**, whose three hypotheses on the property are, for étaleness of
morphisms of algebraic spaces, stability under base change (**Stacks 03FU**), locality at the
target for the fppf precoverage (**Stacks 042B**, through
`AlgebraicGeometry.Space.etaleMorphisms_isLocalAtTarget_fppf`) and stability under composition
(**Stacks 03FT**). -/
theorem isRelativelyEtale_comp
    {𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒜 ⟶ ℬ) (g : ℬ ⟶ 𝒞)
    (hf : IsRelativelyEtale B S hS f) (hg : IsRelativelyEtale B S hS g) :
    IsRelativelyEtale B S hS (f ≫ g) := by
  obtain ⟨hfr, hPf⟩ := hf
  obtain ⟨hgr, hPg⟩ := hg
  have hfgr : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS f g hfr hgr
  exact ⟨hfgr, hasRelativeProperty_comp.{u, u, u + 1, u} B S hS
    (Space.etaleMorphisms B S hS) f g hfr hgr hPf hPg⟩

/-- The identity based functor of a category fibred in groupoids is an equivalence. -/
private theorem isEquivalence_basedFunctor_id
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))

/-- **Relative étaleness is preserved by postcomposition with an equivalence**, in the sense of
Stacks 04XB. Stacks 003Z (2) supplies a quasi-inverse of the equivalence over the site, which is
the horizontal 1-morphism of targets that
`AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences` asks for; the 2-commutativity
isomorphism is the unit, whiskered by the given 1-morphism.

This is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence`. -/
theorem isRelativelyEtale_comp_of_isEquivalence
    {𝒰 𝒦 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒰 ⟶ 𝒦) (e : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e))
    (ha : IsRelativelyEtale B S hS a) :
    IsRelativelyEtale B S hS (a ≫ e) := by
  obtain ⟨F, hF, η, ε, hη, _⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒦.val.p 𝒲.val.p
      𝒦.isFiberedInGroupoids 𝒲.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor e)
      (CatFiberedInGroupoids.homFunctor_comp_p e) he
  have := isEquivalence_basedFunctor_id B S hS 𝒰
  have hbEquiv : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor e) F
      η.symm ε).isEquivalence_inverse
  have hν : ∀ x : 𝒰.val.obj, 𝒦.val.p.IsHomLift (𝟙 (𝒰.val.p.obj x))
      ((Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor a) η).symm.hom.app x) := by
    intro x
    have hb : 𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x) = 𝒰.val.p.obj x :=
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) x
    have h1 : 𝒦.val.p.IsHomLift
        (𝟙 (𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x)))
        (η.inv.app ((CatFiberedInGroupoids.homFunctor a).obj x)) :=
      @IsHomLift.lift_id_inv _ _ _ _ 𝒦.val.p
        (𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x)) _ _
        (η.app ((CatFiberedInGroupoids.homFunctor a).obj x))
        (hη ((CatFiberedInGroupoids.homFunctor a).obj x))
    rw [hb] at h1
    exact h1
  exact isRelativelyEtale_of_equivalences B S hS (a ≫ e) a (BasedFunctor.id 𝒰.val) ⟨F, hF⟩
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor a) η).symm hν) ha

/-- **Relative étaleness is preserved by precomposition with an equivalence**, in the sense of
Stacks 04XB: the equivalence is the horizontal 1-morphism of sources of a 2-commutative square
whose horizontal 1-morphism of targets is the identity.

This is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isEquivalence_comp`. -/
theorem isRelativelyEtale_of_isEquivalence_comp
    {𝒰 𝒦 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (e : 𝒰 ⟶ 𝒦) (q : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e))
    (hq : IsRelativelyEtale B S hS q) :
    IsRelativelyEtale B S hS (e ≫ q) := by
  have := isEquivalence_basedFunctor_id B S hS 𝒲
  exact isRelativelyEtale_of_equivalences B S hS (e ≫ q) q e.hom (BasedFunctor.id 𝒲.val)
    (Iso.refl _) hq

/-- **The backward 1-morphism of a representing equivalence is étale** in the sense of
Stacks 04XB: by the bridge of Stacks 04XB at étaleness for represented source and target it is
enough that the morphism of representing presheaves it induces be étale, and that morphism is the
identity of `F`.

This is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap`. -/
theorem isRelativelyEtale_equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsRelativelyEtale B S hS (equivalenceOverInvMap B S hS F eX) := by
  refine (isRelativelyEtale_iff_isEtale_representingMap B S hS
    (equivalenceOverInvMap B S hS F eX)
    (isRepresentableByAlgebraicSpaces_equivalenceOverInvMap B S hS F hF eX) F F hF hF
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX).2 ?_
  rw [representingMap_equivalenceOverInvMap]
  exact Space.isEtale_id B S hS F

end AlgebraicGeometry.Stack

end

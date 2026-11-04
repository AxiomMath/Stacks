module

public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenary

/-!
# The source of an immersion is Jacobson and pseudo-catenary

**Stacks 0DS2** reads, in part: *"Let `𝒯 ↪ 𝒳` be a locally of finite type monomorphism of
algebraic stacks, with `𝒳` (and thus also `𝒯`) being Jacobson, pseudo-catenary, and locally
Noetherian."* This module supplies the parenthetical for an immersion `j : 𝒳 ⟶ 𝒴`: the Jacobson
and pseudo-catenary conditions pass from the target to the source. The third conjunct, local
Noetherianity, is **Stacks 0CPM** part (1),
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherian_of_isImmersion`.

Both conditions are the existential smooth-scheme-atlas criterion of **Stacks 04YF** —
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` — at a property of schemes: at
`JacobsonSpace` for `AlgebraicGeometry.Stack.AlgebraicStacks.IsJacobson`, and at local
Noetherianity together with `AlgebraicGeometry.Scheme.IsUniversallyCatenary` for
`AlgebraicGeometry.Stack.AlgebraicStacks.IsPseudoCatenary` (**Stacks 0DRU**). Neither needs the
immersion hypothesis itself: both properties are inherited by a scheme locally of finite type
over a scheme having them, and an immersion of algebraic stacks is locally of finite type by
**Stacks 06FV**. So each theorem below is the corresponding transport along a 1-morphism locally
of finite type, evaluated at `AlgebraicGeometry.Stack.AlgebraicStacks`'
`isLocallyOfFiniteType_of_isImmersion`.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSchemeAtlas_of_isLocallyOfFiniteType`: a property of
  schemes inherited along morphisms locally of finite type passes, as the smooth-scheme-atlas
  criterion of Stacks 04YF, from the target of a 1-morphism locally of finite type to its
  source.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isJacobson_of_isImmersion`: the source of an
  immersion with Jacobson target is Jacobson.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isPseudoCatenary_of_isImmersion`: the source of an
  immersion with pseudo-catenary target is pseudo-catenary.

## Implementation notes

`AlgebraicGeometry.Stack.hasPropertyOnSomeSchemeAtlas_of_isLocallyOfFiniteType` is the
property-parametric form of the argument of **Stacks 0DRW**: for a smooth surjective scheme
atlas `a : U ⟶ 𝒴` with `P U`, the apex of the 2-fibre product square of `f` and `a`
(**Stacks 04T2**) has first projection a base change of `a`, hence smooth and surjective, and
second projection a base change of `f`, hence locally of finite type; a smooth surjective scheme
atlas `c : V ⟶ 𝒳 ×_𝒴 U` composed with that second projection is locally of finite type, so by
**Stacks 06FS** and **Stacks 06FM** it is induced by a morphism `V ⟶ U` of the site whose
morphism of schemes is locally of finite type, and `P V` follows. Composing `c` with the first
projection is then the required atlas of `𝒳`.

The property hypothesis is stated for a bare morphism of schemes with
`AlgebraicGeometry.LocallyOfFiniteType` as an explicit argument rather than an instance, since
the morphism it is applied to is produced inside the proof.

Only the Jacobson theorem uses that lemma: being Jacobson is inherited along a morphism locally
of finite type by Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`. For the
pseudo-catenary condition the transport along a 1-morphism locally of finite type is already
proved as **Stacks 0DRW**,
`AlgebraicGeometry.Stack.isPseudoCatenary_of_isLocallyOfFiniteType`, resting on **Stacks 02J9**
(`AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType`), and that statement is
used rather than re-derived.

## References

* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 0DRU](https://stacks.math.columbia.edu/tag/0DRU)
* [Stacks Project, Tag 0DRW](https://stacks.math.columbia.edu/tag/0DRW)
* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of schemes inherited along morphisms locally of finite type passes to the
source of a 1-morphism of algebraic stacks locally of finite type**, read through the
existential smooth-scheme-atlas criterion of **Stacks 04YF**.

This is the argument of **Stacks 0DRW** with the property left free. A smooth surjective scheme
atlas `a : U ⟶ 𝒴` with `P U` is given; the apex of the 2-fibre product square of `f` and `a`
has first projection a base change of `a`, hence smooth and surjective, and second projection a
base change of `f`, hence locally of finite type. A smooth surjective scheme atlas
`c : V ⟶ 𝒳 ×_𝒴 U` composed with the second projection is then locally of finite type, so it
comes from a morphism `V ⟶ U` of the site which is locally of finite type on schemes, and `P V`
follows from `hP`; composing `c` with the first projection is the required atlas of `𝒳`. -/
theorem hasPropertyOnSomeSchemeAtlas_of_isLocallyOfFiniteType (P : ObjectProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), LocallyOfFiniteType g → P Y → P X)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS P 𝒴) :
    HasPropertyOnSomeSchemeAtlas B S hS P 𝒳 := by
  obtain ⟨U, a, haSurj, haSmooth, hU⟩ := h𝒴
  set Q : Bicategory.TwoCommSq f a := twoFibreProductSquareAlgebraicStacks B S hS f a
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f a
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a f Q hQ haSmooth
  have hfstSurj : IsSurjective B S hS Q.fst :=
    isSurjective_of_isTwoFibreProduct B S hS Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) haSurj
  have hsndType : AlgebraicStacks.IsLocallyOfFiniteType B S hS Q.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hf
  obtain ⟨V, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS Q.pt
  obtain ⟨g, hg⟩ := exists_schemeMap_locallyOfFiniteType_of_schemeStackHom B S hS (c ≫ Q.snd)
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS c Q.snd
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcSmooth)) hsndType)
  exact ⟨V, c ≫ Q.fst, isSurjective_comp B S hS c Q.fst hcSurj hfstSurj,
    AlgebraicStacks.isSmooth_comp B S hS c Q.fst hcSmooth hfstSmooth,
    hP ((BigFppfOver.toScheme B S hS).map g) hg hU⟩

namespace AlgebraicStacks

/-- **The source of an immersion of algebraic stacks over `S` with Jacobson target is
Jacobson** — the Jacobson half of the parenthetical of **Stacks 0DS2**.

An immersion is locally of finite type by **Stacks 06FV**, and a scheme locally of finite type
over a Jacobson scheme is Jacobson, so the transport of the smooth-scheme-atlas criterion of
Stacks 04YF along a 1-morphism locally of finite type applies. -/
theorem isJacobson_of_isImmersion {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (j : 𝒳 ⟶ 𝒴)
    (hj : IsImmersion B S hS j) (h𝒴 : IsJacobson B S hS 𝒴) : IsJacobson B S hS 𝒳 :=
  hasPropertyOnSomeSchemeAtlas_of_isLocallyOfFiniteType B S hS
    (fun X : Scheme.{u} => JacobsonSpace X)
    (fun g _ _ => LocallyOfFiniteType.jacobsonSpace g)
    j (isLocallyOfFiniteType_of_isImmersion B S hS j hj) h𝒴

/-- **The source of an immersion of algebraic stacks over `S` with pseudo-catenary target is
pseudo-catenary** — the pseudo-catenary half of the parenthetical of **Stacks 0DS2**.

An immersion is locally of finite type by **Stacks 06FV**, so this is **Stacks 0DRW**, the
transport of pseudo-catenarity to the source of a 1-morphism locally of finite type. -/
theorem isPseudoCatenary_of_isImmersion {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (j : 𝒳 ⟶ 𝒴)
    (hj : IsImmersion B S hS j) (h𝒴 : IsPseudoCatenary B S hS 𝒴) :
    IsPseudoCatenary B S hS 𝒳 :=
  Stack.isPseudoCatenary_of_isLocallyOfFiniteType B S hS j
    (isLocallyOfFiniteType_of_isImmersion B S hS j hj) h𝒴

end AlgebraicStacks

end AlgebraicGeometry.Stack

end

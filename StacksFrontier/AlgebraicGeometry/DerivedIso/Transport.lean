module

public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Scheme
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# `f_*` of the absolute Čech resolution is the relative Čech complex of [Stacks, Tag 01XL]

`Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechComplexCompPushforwardIso`
identifies `f_* 𝔠 ⁼(𝒰, ℱ)` with the Čech complex of the absolute coefficient presheaf
postcomposed with `f_*`, and
`Stacks.AlgebraicGeometry.CechPushforwardComplex.relativeCechPresheaf_eq` says that presheaf *is*
`relativeCechPresheaf f`.  This file composes the two — which needs a reassociation of `⋙`
underneath `CategoryTheory.cechComplexFunctor` — and then transports the result along
`ComplexShape.embeddingUpNat.extendFunctor` and the `CochainComplex.Plus` lift, arriving at the
`relativeCechComplex` that [Stacks, Tag 01XL] states its derived isomorphism for.

## Main definitions

* `pushforwardAbsoluteCechComplexIso`: the `ℕ`-indexed statement, `f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)`
  with the target spelled through `relativeCechPresheaf f`.
* `absoluteCechComplex` and `absoluteCechComplexPlus`: the absolute Čech resolution as a
  `ℤ`-indexed, and then bounded below, complex of `𝒪_X`-modules — the complex that Leray's
  acyclicity lemma ([Stacks, Tag 015E]) consumes.
* `pushforwardAbsoluteCechComplexPlusIso`: **`f_*` of the bounded below absolute Čech resolution
  is the relative Čech complex of [Stacks, Tag 01XL]**, naturally in the quasi-coherent module.

## Implementation notes

**The reassociation.** Rewriting the target of `absoluteCechComplexCompPushforwardIso` along
`relativeCechPresheaf_eq` needs `(H ⋙ K.flip) ⋙ G' ⋙ Φ` and `(K ⋙ G'' ⋙ H'').flip ⋙ Φ` to be
identified, which is expensive on the scheme-level terms.  `flip_comp_whiskerings_comp` is that
identity stated where no scheme data occurs: four abstract categories, a bifunctor, and two
functors, so the `rfl` is checked on variables.  The extra `Φ` puts `cechComplexFunctor` *inside*
the identity being proved abstractly.

**The extension.** `Stacks.DerivedIndexing.mapExtendNatIsoSymm` supplies the commutation of
`ComplexShape.embeddingUpNat.extendFunctor` with
`CategoryTheory.Functor.mapHomologicalComplex`.

**The `Plus` lift.** Both sides land in `CochainComplex.Plus`, and
`CategoryTheory.Functor.fullyFaithfulCancelRight` against the fully faithful inclusion
`CochainComplex.Plus.ι` reduces the isomorphism of the lifts to the isomorphism of the
`ℤ`-indexed complexes, so no `eqToHom` on bound witnesses is needed.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.Tag01XLDerivedIso

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.RelativeCechComplex
open Stacks.AlgebraicGeometry.CechPushforwardComplex

/-! ### The reassociation, where no scheme data occurs -/

section Reassociation

variable {I J J' : Type*} [Category* I] [Category* J] [Category* J']
  {A B E : Type*} [Category* A] [Category* B] [Category* E]

/-- **`Stacks.CechPushforward.flip_comp_whiskerings` with a functor postcomposed.**  The right
hand side is the shape in which a coefficient presheaf is defined — a bifunctor postcomposed by
`G` in one variable, precomposed by `H` in the other, flipped — and the left hand side is the
shape in which the Čech comparison produces it.  At schemes `Φ` is
`CategoryTheory.cechComplexFunctor`. -/
theorem flip_comp_whiskerings_comp (K : I ⥤ J ⥤ A) (G : A ⥤ B) (H : J' ⥤ J) (Φ : (I ⥤ B) ⥤ E) :
    (H ⋙ K.flip) ⋙ (Functor.whiskeringRight I A B).obj G ⋙ Φ =
      (K ⋙ (Functor.whiskeringRight J A B).obj G ⋙
        (Functor.whiskeringLeft J' J B).obj H).flip ⋙ Φ :=
  rfl

end Reassociation

variable {X S : Scheme.{u}}

/-! ### The `ℕ`-indexed statement -/

/-- **`f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)`.**  Applying `f_*` termwise to the absolute Čech complex of
the family `Over.mk (T.f i)` is the relative Čech complex of [Stacks, Tag 01XL], naturally in the
quasi-coherent module.  This is the "equality of complexes" the source's proof asserts; it is an
isomorphism because `f_*` commutes with the products defining the terms only up to the
comparison map.

No hypothesis is placed on `f`, on `T` or on the schemes. -/
noncomputable def pushforwardAbsoluteCechComplexIso (f : X ⟶ S) (T : X.AffineOpenCover) :
    absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ⋙
        (Scheme.Modules.pushforward f).mapHomologicalComplex _ ≅
      relativeCechPresheaf f ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) :=
  absoluteCechComplexCompPushforwardIso f T ≪≫
    eqToIso (flip_comp_whiskerings_comp (relativeMonad X) (Scheme.Modules.pushforward f)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))))

/-! ### Transport along the extension, where no scheme data occurs -/

section ExtendTransport

variable {𝒞 : Type*} [Category* 𝒞] {A B : Type*} [Category* A] [Category* B]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A] [HasZeroObject B]
  {I I' : Type*} {c : ComplexShape I} {c' : ComplexShape I'}

/-- **A termwise comparison transported along the extension of complexes.**  If applying `G`
termwise to the complexes of `F` gives the complexes of `F'`, then the same holds after extending
both along an embedding `e` of complex shapes.  Stated abstractly, so that the reassociations
involved are checked on variables. -/
noncomputable def compExtendFunctorIso (e : c.Embedding c')
    (F : 𝒞 ⥤ HomologicalComplex A c) (F' : 𝒞 ⥤ HomologicalComplex B c)
    (G : A ⥤ B) [G.PreservesZeroMorphisms] (α : F ⋙ G.mapHomologicalComplex c ≅ F') :
    (F ⋙ e.extendFunctor A) ⋙ G.mapHomologicalComplex c' ≅ F' ⋙ e.extendFunctor B :=
  Functor.isoWhiskerLeft F (Stacks.DerivedIndexing.mapExtendNatIsoSymm G e) ≪≫
    Functor.isoWhiskerRight α (e.extendFunctor B)

end ExtendTransport

/-! ### The bounded below absolute Čech resolution and the transport to [Stacks, Tag 01XL] -/

/-- **The absolute Čech resolution of a finite affine open cover, as a bounded below complex of
`𝒪_X`-modules.**  This is `𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 01XL], in the indexing that Leray's
acyclicity lemma ([Stacks, Tag 015E]) consumes: the `ℕ`-indexed Čech complex extended along
`ComplexShape.embeddingUpNat` and bounded below at `0`.  It is the exact absolute analogue of
`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechComplex`. -/
noncomputable def absoluteCechComplexPlus (T : X.AffineOpenCover) [Fintype T.I₀] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _
    (absoluteCechPresheaf X ⋙
      CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ⋙
      ComplexShape.embeddingUpNat.extendFunctor X.Modules)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj
          ((absoluteCechPresheaf X).obj F)).extend ComplexShape.embeddingUpNat) 0
      infer_instance⟩)

/-- The `ℤ`-indexed form of `pushforwardAbsoluteCechComplexIso`. -/
noncomputable def pushforwardAbsoluteCechComplexExtendIso (f : X ⟶ S) (T : X.AffineOpenCover) :
    ((absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules) ⋙
          (Scheme.Modules.pushforward f).mapHomologicalComplex _ ≅
      (relativeCechPresheaf f ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor S.Modules :=
  compExtendFunctorIso ComplexShape.embeddingUpNat _ _ (Scheme.Modules.pushforward f)
    (pushforwardAbsoluteCechComplexIso f T)

/-- **`f_*` of the bounded below absolute Čech resolution IS the relative Čech complex of
[Stacks, Tag 01XL]**, naturally in the quasi-coherent `𝒪_X`-module.  This is the "equality of
complexes" the source's proof asserts, in the indexing in which [Stacks, Tag 01XL] states its
derived isomorphism, and it is what lets Leray's acyclicity lemma — which is about the absolute
complex in `X.Modules` — say anything about the relative complex in `S.Modules`.

No hypothesis is placed on `f`, on `T` or on the schemes. -/
noncomputable def pushforwardAbsoluteCechComplexPlusIso (f : X ⟶ S) (T : X.AffineOpenCover)
    [Fintype T.I₀] :
    absoluteCechComplexPlus T ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ≅
      relativeCechComplex f T :=
  Functor.fullyFaithfulCancelRight (CochainComplex.Plus.ι S.Modules)
    (pushforwardAbsoluteCechComplexExtendIso f T)

end Stacks.AlgebraicGeometry.Tag01XLDerivedIso

end

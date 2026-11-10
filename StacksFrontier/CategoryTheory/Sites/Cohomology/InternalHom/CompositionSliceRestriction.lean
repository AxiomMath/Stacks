module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction

/-!
# Composition of internal Hom complexes commutes with restriction to a slice site

Let `(C, O)` be a ringed site, `U` an object of `C` and `K`, `L`, `M` complexes of `O`-modules.
Restriction to the slice site `C/U` carries the internal Hom complexes to the internal Hom
complexes of the restrictions, by the isomorphism
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` of Stacks 08JB, and this
isomorphism carries the composition of local sections, which characterises the composition
morphism of Stacks 0A91, to the composition of their restrictions: for local sections `β` of
`SheafHom(L, M)` and `γ` of `SheafHom(K, L)`,

`(β ∘ γ)|_U = β|_U ∘ γ|_U`.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_isInternalHomRestrictionMap`: a map of
  internal Hom complexes which is the restriction map in the sense of
  `AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap` does not change the value of a local
  section on a local section of the source: evaluating the restricted section over an object of
  the iterated slice is evaluating the original over the underlying object.
* `AlgebraicGeometry.RingedSite.compositionSection_isInternalHomRestrictionMap`: restriction to
  a slice site carries composition to composition, for an arbitrary triple of restriction maps.
* `AlgebraicGeometry.RingedSite.compositionSection_sheafHomRestrictionComplexIso`: the same for
  the canonical restriction isomorphism.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- Let `f` be the restriction map of internal Hom complexes in the sense of
`AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap`. For objects `V`, `W` of `C/U` with an
arrow `i : W ⟶ V`, a degree-`n` section `s` of `SheafHom(A, B)` over `V.left` and a degree-`p`
section `x` of `A` over `W.left`, evaluating `f(s)` on `x` along `i` gives the same section of `B`
as evaluating `s` on `x` along the underlying arrow `i.left : W.left ⟶ V.left` of `C`. -/
theorem applyHomSectionOver_isInternalHomRestrictionMap
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {f : restrictComplex X (sheafHomComplex X A B).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X A U) (restrictComplex X B U)).obj}
    (hf : IsInternalHomRestrictionMap X U A B f)
    (V W : Over U) (i : W ⟶ V) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op V.left))
    (x : (A.X p).val.obj (op W.left)) :
    applyHomSectionOver (X.over U)
        (sheafHomComplex (X.over U) (restrictComplex X A U) (restrictComplex X B U))
        V W i n p q hpq ((f.f n).val.app (op V) s) x =
      applyHomSectionOver X (sheafHomComplex X A B) V.left W.left i.left n p q hpq s x := by
  change ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex (X.over U) (restrictComplex X A U)
        (restrictComplex X B U)).sectionsIso V).hom.f n)
      ((f.f n).val.app (op V) s)).v p q hpq).val.app (op (Over.mk i)) x = _
  rw [hf (op V) n p q hpq s]
  exact Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app X U (A.X p) (B.X q) (op V)
    (((AddCommGrpCat.Hom.hom (((sheafHomComplex X A B).sectionsIso V.left).hom.f n) s).v
      p q hpq).val) (op (Over.mk i)) x

/-- Restriction to a slice site carries the composition of local sections of internal Hom
complexes to the composition of their restrictions: for a degree-`p` section `β` of
`SheafHom(L, M)` and a degree-`q` section `γ` of `SheafHom(K, L)` over an object `V` of `C/U`,

`(β ∘ γ)|_U = β|_U ∘ γ|_U`,

where the three restriction maps are arbitrary maps with the property
`AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap`. -/
theorem compositionSection_isInternalHomRestrictionMap
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {fKL : restrictComplex X (sheafHomComplex X K L).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X K U) (restrictComplex X L U)).obj}
    {fLM : restrictComplex X (sheafHomComplex X L M).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X L U) (restrictComplex X M U)).obj}
    {fKM : restrictComplex X (sheafHomComplex X K M).obj U ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X K U) (restrictComplex X M U)).obj}
    (hKL : IsInternalHomRestrictionMap X U K L fKL)
    (hLM : IsInternalHomRestrictionMap X U L M fLM)
    (hKM : IsInternalHomRestrictionMap X U K M fKM)
    (V : Over U) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op V.left))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op V.left)) :
    ((fKM.f n).val.app (op V) (compositionSection X V.left p q n hn β γ)) =
      compositionSection (X.over U) V p q n hn
        ((fLM.f p).val.app (op V) β) ((fKL.f q).val.app (op V) γ) := by
  refine homSection_ext (X.over U)
    (sheafHomComplex (X.over U) (restrictComplex X K U) (restrictComplex X M U))
    V n fun r t hrt W i x ↦ ?_
  rw [applyHomSectionOver_isInternalHomRestrictionMap X U hKM V W i n r t hrt
      (compositionSection X V.left p q n hn β γ) x,
    compositionSection_applyOver X V.left W.left i.left p q n r (r + q) t hn rfl (by omega)
      β γ x,
    compositionSection_applyOver (X.over U) V W i p q n r (r + q) t hn rfl (by omega)
      ((fLM.f p).val.app (op V) β) ((fKL.f q).val.app (op V) γ) x,
    applyHomSectionOver_isInternalHomRestrictionMap X U hKL V W i q r (r + q) rfl γ x,
    applyHomSectionOver_isInternalHomRestrictionMap X U hLM V W i p (r + q) t (by omega) β _]

/-- The canonical restriction isomorphism
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` of internal Hom complexes carries the
composite of two homogeneous local sections to the composite of their restrictions. -/
theorem compositionSection_sheafHomRestrictionComplexIso
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : Over U) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op V.left))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op V.left)) :
    (((sheafHomRestrictionComplexIso X U K M).hom.f n).val.app (op V)
        (compositionSection X V.left p q n hn β γ)) =
      compositionSection (X.over U) V p q n hn
        (((sheafHomRestrictionComplexIso X U L M).hom.f p).val.app (op V) β)
        (((sheafHomRestrictionComplexIso X U K L).hom.f q).val.app (op V) γ) :=
  compositionSection_isInternalHomRestrictionMap X U
    (sheafHomRestrictionComplexIso_isRestriction X U K L)
    (sheafHomRestrictionComplexIso_isRestriction X U L M)
    (sheafHomRestrictionComplexIso_isRestriction X U K M) V p q n hn β γ

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.BigFppfSiteEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDataReindex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective fppf descent for affine morphisms

Let `S` be a scheme and let `{X i ⟶ S}` be a covering family of `S` for the fppf topology, that
is a family of flat morphisms locally of finite presentation whose images cover `S`. A descent
datum relative to that family all of whose structure morphisms `V i ⟶ X i` are affine is
effective. Every fppf covering family is an fpqc covering family, flat morphisms locally of
finite presentation being open, so this is
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom` — Stacks 0245 — read through
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`.

Two refinements of 0245 are needed before it can be used in this form. The index type of the
family is freed from the universe of the schemes: any `u`-small index type is admitted, by
reindexing along `Shrink`. In particular a one-member family is admitted, and so the single
morphism case reads: a descent datum relative to a surjective flat morphism locally of finite
presentation, with affine structure morphism, is effective. That case asks for no
quasi-compactness, unlike `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom`, which
covers a single fpqc covering instead.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_small`: effectivity along an
  fpqc covering family indexed by any `u`-small type.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_mem_fppfPrecoverage`:
  **effectivity along an fppf covering family.**
* `AlgebraicGeometry.DescentDatum.isFamilyEffective_of_isAffineHom_of_locallyOfFinitePresentation`
  and its companion
  `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_locallyOfFinitePresentation`: the
  single-morphism case, for a surjective flat morphism locally of finite presentation.
* `AlgebraicGeometry.BigFppfOver.exists_objectOver_iso_pullback_of_isAffineHom`: descending a
  morphism inside a big fppf category over `S` along a surjective flat morphism locally of finite
  presentation, with no effectivity hypothesis left to supply.

## Implementation notes

Effectivity relative to a family is invariant under reindexing the family along a bijection of
index types, and the presieve the family generates is unchanged, so the passage between an
arbitrary `u`-small index type and its `Shrink` costs nothing beyond
`AlgebraicGeometry.DescentData.isFamilyEffective_of_reindex` and
`AlgebraicGeometry.DescentData.ofArrows_reindex`.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}

/-- **Effective fpqc descent for affine morphisms, along a family indexed by any `u`-small
type.** A descent datum relative to an fpqc covering family of `S` whose structure morphisms are
affine is effective. -/
theorem isFamilyEffective_of_isAffineHom_of_small [Small.{u} ι] (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) (D : DescentData f)
    (hD : ∀ i, IsAffineHom (D.obj i).hom) : D.IsFamilyEffective := by
  let e : Shrink.{u} ι ≃ ι := (equivShrink ι).symm
  have hf' : Presieve.ofArrows (fun j ↦ X (e j)) (fun j ↦ f (e j)) ∈
      Scheme.fpqcPrecoverage S := by
    rw [ofArrows_reindex]
    exact hf
  exact isFamilyEffective_of_reindex e
    (isFamilyEffective_of_isAffineHom (fun j ↦ f (e j)) hf' (D.reindex e) fun j ↦ hD (e j))

/-- **Effective fppf descent for affine morphisms.** A descent datum relative to a covering
family of `S` for the fppf topology whose structure morphisms are affine is effective: it is
isomorphic to the canonical descent datum of a scheme over `S`. -/
theorem isFamilyEffective_of_isAffineHom_of_mem_fppfPrecoverage [Small.{u} ι] (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) (D : DescentData f)
    (hD : ∀ i, IsAffineHom (D.obj i).hom) : D.IsFamilyEffective :=
  isFamilyEffective_of_isAffineHom_of_small f
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hf) D hD

end DescentData

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- **Effective descent for affine morphisms along a single surjective flat morphism locally of
finite presentation.** Such a morphism is an fppf covering on its own, so a descent datum
relative to it whose structure morphism is affine is effective. -/
@[sga "3 IV 4.7" "partial"]
theorem isFamilyEffective_of_isAffineHom_of_locallyOfFinitePresentation [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] (D : DescentDatum f) (haff : IsAffineHom D.over.hom) :
    DescentData.IsFamilyEffective D := by
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) ∈ Scheme.fppfPrecoverage S := by
    rw [DescentData.ofArrows_const_eq_singleton]
    exact f.singleton_mem_fppfPrecoverage
  exact DescentData.isFamilyEffective_of_isAffineHom_of_mem_fppfPrecoverage
    (fun _ : Unit ↦ f) hcov D fun _ ↦ haff

/-- A descent datum relative to a surjective flat morphism locally of finite presentation, whose
structure morphism is affine, is the canonical descent datum of a scheme over the base. -/
theorem isEffective_of_isAffineHom_of_locallyOfFinitePresentation [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] (D : DescentDatum f) (haff : IsAffineHom D.over.hom) :
    DescentData.IsEffective D :=
  DescentData.isEffective_of_isFamilyEffective
    (isFamilyEffective_of_isAffineHom_of_locallyOfFinitePresentation D haff)

end DescentDatum

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Descending a morphism inside a big fppf category over `S`, along a surjective flat
morphism locally of finite presentation whose descent datum has affine structure morphism.** This
is `AlgebraicGeometry.BigFppfOver.exists_objectOver_iso_pullback_of_isFamilyEffective` with its
effectivity hypothesis discharged by effective fppf descent for affine morphisms. -/
theorem exists_objectOver_iso_pullback_of_isAffineHom
    {T T' U V : BigFppfOver B S hS} (f : T' ⟶ T) (p : V ⟶ T') (q : V ⟶ U)
    (hff : Flat ((toScheme B S hS).map f)) (hfs : Surjective ((toScheme B S hS).map f))
    (hfp : LocallyOfFinitePresentation ((toScheme B S hS).map f))
    (hp : IsAffineHom ((toScheme B S hS).map p))
    (φ : Over.mk (prod.map (structureMap ((toScheme B S hS).map f)
          (Over.mk ((toScheme B S hS).map p)))
        (𝟙 (Over.mk ((toScheme B S hS).map f)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk ((toScheme B S hS).map f)))
        (structureMap ((toScheme B S hS).map f) (Over.mk ((toScheme B S hS).map p)))))
    (cocycle : prod.map φ.hom.left (𝟙 (Over.mk ((toScheme B S hS).map f))) ≫
        prodMapLastTwo φ.hom.left = prodMapFirstThird φ.hom.left)
    (hq : (DescentDatum.mk' (f := (toScheme B S hS).map f)
      (Over.mk ((toScheme B S hS).map p)) φ cocycle).IsGluingInvariant
      fun _ ↦ (toScheme B S hS).map q) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (α : pullback f w ≅ V),
      α.hom ≫ p = pullback.fst f w ∧
      pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
        pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q := by
  have := hff
  have := hfs
  have := hfp
  exact exists_objectOver_iso_pullback_of_isFamilyEffective f p q hff hfs φ cocycle
    (DescentDatum.isFamilyEffective_of_isAffineHom_of_locallyOfFinitePresentation _ hp) hq

end BigFppfOver

end AlgebraicGeometry

end

end

module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtBoundary

/-!
# `Ext¹` is computed in a subcategory closed under extensions

Let `Φ : 𝒜 ⥤ 𝒞` be a fully faithful exact functor of abelian categories whose essential image
is closed under extensions. Then the canonical maps

`Ext¹_𝒜(X, Y) ⟶ Ext¹_𝒞(Φ X, Φ Y)`

of `CategoryTheory.Functor.mapExtAddHom` are **bijective**. The case this is written for is the
inclusion of a weak Serre subcategory, where closure under extensions is one of the defining
closure properties.

Degree `1` is the exact range of the statement. Degree `0` is the map on `Hom` and is bijective
from full faithfulness alone, with no closure property
(`CategoryTheory.Abelian.Ext.mapExactFunctor₀`). From degree `2` on it is false, and the
counterexample is in this library: for the `I`-power-torsion modules over a commutative ring,
`Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule` exhibits a ring, a principal
ideal and two torsion modules for which the comparison on `Ext²` misses a class — and that
subcategory is a Serre subcategory, so closed under extensions a fortiori. Closure under
extensions therefore buys exactly one positive degree; the higher degrees need a comparison of
derived categories instead.

Why the bound is sharp is visible in the proof. `Ext¹` is the group of Yoneda extensions
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`), so a class of
`Ext¹_𝒞(Φ X, Φ Y)` is the class of a short exact sequence `0 ⟶ Φ Y ⟶ E ⟶ Φ X ⟶ 0` whose outer
terms lie in the essential image; closure under extensions puts `E` there too, and the sequence
descends along `Φ` because `Φ` is full and reflects short exactness. A class of `Ext^n` for
`n ≥ 2` is represented instead by a Yoneda extension of length `n`, whose `n - 1` intermediate
terms are constrained by no closure property of the image.

## Main results

* `CategoryTheory.Functor.surjective_mapExtAddHom_one_of_essImage_shortExact` — closure of the
  essential image under extensions makes the comparison surjective in degree `1`.
* `CategoryTheory.Functor.bijective_mapExtAddHom_one_of_essImage_shortExact` — together with
  injectivity, which is `CategoryTheory.Functor.extMap_injective_of_fullyFaithful` and needs
  only full faithfulness, the comparison is bijective in degree `1`.

## Implementation notes

The hypotheses are stated for a functor rather than for the inclusion `P.ι` of an
`ObjectProperty`, which is the case they are used in, because a statement about `P.ι` has to
carry `Abelian P.FullSubcategory` as an instance argument, and an *opaque* such argument
supplies a `Preadditive P.FullSubcategory` through `Abelian.toPreadditive` which is not the
`CategoryTheory.Preadditive.fullSubcategory` that Mathlib's `Additive` instance for `P.ι` is
stated against. `Functor.mapExtAddHom` then cannot find `P.ι.Additive` and no binder repairs it,
the two instances being irreducibly different terms. Over an abstract `𝒜` the question does not
arise: the caller owns the `Abelian` instance and the one `Additive` instance it determines.

`Dualizing.bijective_mapExt_one_powerTorsionModule` is this statement at one instantiation, the
inclusion of the `I`-power-torsion modules, and the proof generalized here is its proof. It is
nevertheless not rederived from this lemma: importing this module into
`StacksFrontier/RingTheory/Dualizing/DerivedTorsion.lean` makes an unrelated `Module.IsTorsionFree`
instance search later in that file exceed its `synthInstance` heartbeat budget. This happens
with the import as the only change and every proof in that file untouched, so the cause is
the enlarged instance context and not the rederivation; doing the rederivation
therefore means first restructuring that search, which is work in another chapter.

## References

* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v v' u u'

namespace CategoryTheory.Functor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {𝒞 : Type u'} [Category.{v'} 𝒞] [Abelian 𝒞]
  (Φ : 𝒜 ⥤ 𝒞) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [Φ.Full] [Φ.Faithful] [HasExt.{w} 𝒜] [HasExt.{w'} 𝒞]

/-- **A subcategory closed under extensions receives every class of `Ext¹`.** If the essential
image of a fully faithful exact functor `Φ` is closed under extensions, then
`Ext¹_𝒜(X, Y) ⟶ Ext¹_𝒞(Φ X, Φ Y)` is surjective.

A class of `Ext¹_𝒞(Φ X, Φ Y)` is the class of a short exact sequence `0 ⟶ Φ Y ⟶ E ⟶ Φ X ⟶ 0`
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`). Its outer terms
lie in the essential image, hence so does `E`; the two maps therefore descend along the full
functor `Φ` after composing with an isomorphism `Φ E' ≅ E`, the resulting short complex of `𝒜`
is short exact because a faithful exact functor reflects short exactness, and its class maps to
the given one, the two sequences being isomorphic over their end terms. -/
public lemma surjective_mapExtAddHom_one_of_essImage_shortExact
    (hext : ∀ S : ShortComplex 𝒞, S.ShortExact → Φ.essImage S.X₁ → Φ.essImage S.X₃ →
      Φ.essImage S.X₂)
    (X Y : 𝒜) :
    Function.Surjective (Φ.mapExtAddHom.{w, w'} X Y 1) := by
  intro x
  obtain ⟨E, i, p, w, hE, hx⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum 𝒞 (Φ.obj X) (Φ.obj Y)).1 x
  obtain ⟨E', ⟨e⟩⟩ := hext _ hE (Φ.obj_mem_essImage Y) (Φ.obj_mem_essImage X)
  let j : Y ⟶ E' := Φ.preimage (i ≫ e.inv)
  let q : E' ⟶ X := Φ.preimage (e.hom ≫ p)
  have hj : Φ.map j = i ≫ e.inv := Φ.map_preimage _
  have hq : Φ.map q = e.hom ≫ p := Φ.map_preimage _
  have hw : j ≫ q = 0 := by
    apply Φ.map_injective
    rwa [Φ.map_comp, hj, hq, Φ.map_zero, Category.assoc, Iso.inv_hom_id_assoc]
  let S : ShortComplex 𝒜 := ShortComplex.mk j q hw
  have hiso : ShortComplex.mk i p w ≅ S.map Φ :=
    ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _)
      (by simp [S, hj]) (by simp [S, hq])
  have hmapS : (S.map Φ).ShortExact := ShortComplex.shortExact_of_iso hiso hE
  have hS : S.ShortExact := (CategoryTheory.ShortExact.shortExact_map_iff Φ).1 hmapS
  refine ⟨hS.extClass, ?_⟩
  rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_extClass]
  refine Eq.trans ?_ hx
  exact (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum 𝒞 (Φ.obj X) (Φ.obj Y)).2.1
    (Φ.obj E') E (Φ.map j) (Φ.map q) (S.map Φ).zero i p w hmapS hE |>.2
    ⟨e, by rw [hj, Category.assoc, Iso.inv_hom_id, Category.comp_id], by rw [hq]⟩

/-- **`Ext¹` is computed in a subcategory closed under extensions.** If the essential image of a
fully faithful exact functor `Φ` is closed under extensions, then the comparison
`Ext¹_𝒜(X, Y) ⟶ Ext¹_𝒞(Φ X, Φ Y)` is bijective.

Injectivity is `CategoryTheory.Functor.extMap_injective_of_fullyFaithful`, which uses only that
`Φ` is fully faithful and exact; surjectivity is
`CategoryTheory.Functor.surjective_mapExtAddHom_one_of_essImage_shortExact` and is where closure
under extensions enters. -/
public lemma bijective_mapExtAddHom_one_of_essImage_shortExact
    (hext : ∀ S : ShortComplex 𝒞, S.ShortExact → Φ.essImage S.X₁ → Φ.essImage S.X₃ →
      Φ.essImage S.X₂)
    (X Y : 𝒜) :
    Function.Bijective (Φ.mapExtAddHom.{w, w'} X Y 1) :=
  ⟨Φ.extMap_injective_of_fullyFaithful X Y,
    Φ.surjective_mapExtAddHom_one_of_essImage_shortExact hext X Y⟩

end CategoryTheory.Functor

end

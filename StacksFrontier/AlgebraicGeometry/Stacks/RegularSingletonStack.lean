module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack

/-!
# Regularity of a reduced locally Noetherian algebraic stack with one point (Stacks 06MV)

**Stacks 06MV** asserts that a reduced, locally Noetherian algebraic stack `𝒵` whose space of
points is a singleton is regular. This is the hypothesis under which the residual gerbe of
**Stacks 06MU**, when it exists, is a regular algebraic stack.

A locally Noetherian atlas `V ⟶ 𝒵` and a surjective flat 1-morphism `Spec k ⟶ 𝒵` out of the
spectrum of a field, which **Stacks 06MN** extracts from reducedness and singletonness, present
the 2-fibre product `𝒬 = Spec k ×_𝒵 V`, an algebraic stack representable by an algebraic space
because both legs of the cospan are. Its projection to `Spec k` is smooth, being a base change of
the atlas, so the representing space is regular by **Stacks 06M1**; its projection to `V` is flat
and surjective, being a base change of the cover, so `V` is regular by **Stacks 06MK**.

## Main definitions

* `AlgebraicGeometry.Stack.IsRegularStack`: regularity of an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isRegularStack_of_isReducedLocallyNoetherianWithUniquePoint`:
  **Stacks 06MV**.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_isSmooth_over_fieldSpectrum`:
  an algebraic space smooth over a site object whose underlying scheme is *isomorphic* to the
  spectrum of a field is regular.

## Implementation notes

Regularity of an algebraic stack is asked through the existential scheme criterion
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of **Stacks 04YF**, as reducedness and
local Noetherianity are in `AlgebraicGeometry.Stack.ReducedUniquePointStack`; regularity of
schemes is local for the smooth precoverage by **Stacks 036D**, so the criterion applies to it
without further hypotheses.

The source proof takes its surjective flat cover by the spectrum of a field from condition (2)
of **Stacks 06MP**, which also makes the cover locally of finite presentation and so lets it
appeal to the form of **Stacks 06MK** that deduces local Noetherianity of the target. Here local
Noetherianity of the target is already a hypothesis, so the weaker cover supplied by
condition (2) of **Stacks 06MN** — surjective and flat, with no finiteness — suffices against
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat`, the form of
Stacks 06MK in which local Noetherianity of the target is assumed rather than deduced. Local
finite presentation plays no other role in the source argument.

The atlas witnessing the conclusion is the one the local Noetherianity hypothesis supplies, so
no passage between the some-atlas and every-atlas forms of Stacks 04YF is required.

The library's form of **Stacks 06M1** requires the underlying scheme of the site object to be
*equal* to the spectrum of the field, which an `AlgebraicGeometry.Stack.FieldSpectrum` supplies
only up to isomorphism. The variant proved here replaces that equality by an isomorphism, which
is smooth because it is an open immersion; this is a strict generalisation of
`AlgebraicGeometry.Space.isRegular_of_isSmooth_over_field` and is proved the same way.

## References

* [Stacks Project, Tag 036D](https://stacks.math.columbia.edu/tag/036D)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06MK](https://stacks.math.columbia.edu/tag/06MK)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06MV](https://stacks.math.columbia.edu/tag/06MV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Space

/-- An algebraic space over `S` which is smooth over an object of the big fppf site whose
underlying scheme is isomorphic to the spectrum of a field is regular.

This is `AlgebraicGeometry.Space.isRegular_of_isSmooth_over_field` (**Stacks 06M1**) with the
equality identifying the underlying scheme weakened to an isomorphism. -/
theorem hasEtaleLocalProperty_isRegular_of_isSmooth_over_fieldSpectrum
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (k : Type u) [Field k]
    (T : BigFppfOver B S hS)
    (hT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj T) (hf : IsSmooth B S hS f) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsRegular X) := by
  obtain ⟨U, a, hsurj, hetale⟩ := hF.exists_atlas
  refine ⟨U, a, hsurj, hetale, ?_⟩
  have hsmooth : Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
    hf U T a (𝟙 (yoneda.obj T)) (yoneda.preimage (a ≫ f)) hetale
      (AlgebraicGeometry.presheaf_id_of_iso B S hS _
        (fun {_ _} g hg ↦ by
          have := hg
          have : IsIso ((BigFppfOver.toScheme B S hS).map g) := inferInstance
          exact inferInstanceAs (Etale ((BigFppfOver.toScheme B S hS).map g))) T)
      (by rw [yoneda.map_preimage]; simp)
  have : Smooth hT.hom := inferInstance
  exact AlgebraicGeometry.isRegular_of_smooth_over_field (k := k)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f)) ≫ hT.hom)

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` is *regular* when some smooth surjective scheme atlas of it has
regular underlying scheme. This is the existential scheme criterion of **Stacks 04YF** at
regularity, which is local for the smooth precoverage by **Stacks 036D**. -/
abbrev IsRegularStack (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  HasPropertyOnSomeSchemeAtlas B S hS (fun X : Scheme.{u} => IsRegular X) 𝒵

/-- A reduced, locally Noetherian algebraic stack over `S` whose space of points of
**Stacks 04XG** is a singleton is regular.

Reducedness and singletonness give a surjective flat 1-morphism `Spec k ⟶ 𝒵` out of the spectrum
of a field by **Stacks 06MN**. Against a locally Noetherian smooth surjective scheme atlas
`V ⟶ 𝒵`, the 2-fibre product `Spec k ×_𝒵 V` is represented by an algebraic space which is smooth
over `Spec k`, hence regular by **Stacks 06M1**, and whose projection to `V` is flat and
surjective, so `V` is regular by **Stacks 06MK**. -/
@[stacks 06MV]
theorem isRegularStack_of_isReducedLocallyNoetherianWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵) :
    IsRegularStack B S hS 𝒵 := by
  obtain ⟨hred, hnoeth⟩ := h
  obtain ⟨F, f, hsurj, hflat⟩ :=
    (isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵).mp hred
  obtain ⟨V, b, hbSurj, hbSmooth, hVnoeth⟩ := hnoeth
  refine ⟨V, b, hbSurj, hbSmooth, ?_⟩
  set Q := twoFibreProductSquareAlgebraicStacks B S hS f b
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f b
  have hbrep : IsRepresentableByAlgebraicSpaces B S hS b.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) b.hom
  have hrep : IsRepresentableByAlgebraicSpace B S hS Q.pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒵.val
      (schemeStack.{u, w} B S hS F.base).val (schemeStack.{u, w} B S hS V).val
      f.hom.hom b.hom.hom hbrep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  obtain ⟨R, hR, ⟨eR⟩⟩ := hrep
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS b f _ hQ hbSmooth
  have hsndFlat : AlgebraicStacks.IsFlat B S hS Q.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS f b Q.swap (Bicategory.isTwoFibreProduct_swap hQ) hflat
  have hsndSurj : IsSurjective B S hS Q.snd :=
    isSurjective_of_isTwoFibreProduct B S hS _ hQ hsurj
  have hm := isSmooth_representingMap_of_isSmooth B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) R (yoneda.obj F.base) hR
    (isAlgebraicSpace_yoneda B S hS F.base) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver F.base) _ hfstSmooth
  have hn := isFlat_representingMap_of_isFlat.{u, w} B S hS R (yoneda.obj V) hR
    (isAlgebraicSpace_yoneda B S hS V) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver V) _ hsndFlat
  have hnsurj := isSurjective_representingMap_of_isSurjective B S hS R (yoneda.obj V) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver V) _ hsndSurj
  have hRreg := Space.hasEtaleLocalProperty_isRegular_of_isSmooth_over_fieldSpectrum
    B S hS F.carrier F.base F.isSpec hR _ hm
  have hV (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage] :
      Space.HasEtaleLocalProperty B S hS (yoneda.obj V) P ↔
      P ((BigFppfOver.toScheme B S hS).obj V) :=
    Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V) P V (Iso.refl _)
  exact (hV _).mp (Space.hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat B S hS hR
    (isAlgebraicSpace_yoneda B S hS V) _ hn hnsurj ((hV _).mpr hVnoeth) hRreg)

end Stack

end AlgebraicGeometry

end

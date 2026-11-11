module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldPointFibreChartTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SliceFibreFieldPoint

/-!
# The fibre of the Stacks 06MD slice, read inside the fibre of the chart

The chart construction of **Stacks 06N3** holds two presentations of one algebraic space, and
until now nothing identified them.

* **Stacks 06MD** slices an algebraic space `U` with a 1-morphism `f : U ⟶ 𝒳` by `r` global
  regular functions `c₁, …, c_r`, producing an *open* subspace `V ⊆ U` and the slice
  `Zsl = V(c₁, …, c_r) ∩ V`, i.e. `AlgebraicGeometry.Stack.zeroLocusOnOpen`. The unramifiedness
  clause of **Stacks 06N2** is then wanted at the fibre `Zsl ×_𝒳 Spec k` of the slice over the
  field-valued point, through
  `AlgebraicGeometry.Stack.exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt`, which
  asks for that fibre's representing algebraic space together with a presheaf isomorphic to it
  carrying the structure morphism to `Spec k`.
* The étale chart at which the unramifiedness is actually checked,
  `AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`,
  lives inside `Z ∩ p⁻¹V`, where `Fsp` represents the fibre `F = U ×_𝒳 Spec k` of the *chart*,
  `p : Fsp ⟶ U` is its projection and `Z = V(p^*c₁, …, p^*c_r) ⊆ Fsp` is the zero locus of the
  pulled-back functions. It has to: the slicing sequence of **Stacks 06MD** and the closed point
  of **Stacks 056U** are produced on an affine étale chart of `Fsp`, because `V` is only cut out
  afterwards, out of that sequence.

The two are identified here, compatibly with the structure morphism to `Spec k`:

`Zsl ×_𝒳 Spec k ≅ V(p^*c₁, …, p^*c_r) ∩ p⁻¹V` inside `Fsp`.

Neither half of the identification is an instance of an existing result. The leg that compares
representing algebraic spaces of a base change of a *subspace* of the source,
`AlgebraicGeometry.Stack.exists_iso_representingMap_restrictionInnerSquare_fst`, is stated at the
inclusion `Z.ι` of a subfunctor of `U`, whereas the slice reaches `U` through the composite
`Zsl.ι ≫ V.ι` of two inclusions — and that composite is not the inclusion of a subfunctor of
`U` on the nose, so the stack whose fibre is being taken is a different one. The first result
below is therefore the general form: an arbitrary morphism of algebraic spaces in the role of the
restriction. And the identification of `Zsl ×_𝒳 Spec k` with a subspace of `Fsp` compares the
*structure morphism* to `Spec k`, not merely the projection to `U`, so the legs of the cospan
have to be exchanged once on representing presheaves —
`AlgebraicGeometry.Stack.exists_isIso_representingMap_twoFibreProductSquare_swap`.

## The two presentations of an intersection

Inside `Fsp` the fibre of the slice arrives as `p⁻¹V` cut down by `Z`, i.e. as
`CategoryTheory.Subfunctor.preimage` of the open subspace along the closed immersion, whereas the
slice itself is `V(c₁, …, c_r)` cut down by `V`, the preimage taken the other way round. The two
spellings of one intersection are not the same object — they sit inside different ambient
presheaves — and the first two results below are the comparison, at the level of subfunctors of a
presheaf of types and with no geometry in them: two inverse images of each other along the two
inclusions are two fibre products of one cospan, **Stacks 083Q**, hence uniquely isomorphic over
the ambient presheaf; and the intersection of a subfunctor with the inverse image of another is
the inverse image of their intersection, by pasting two such squares.

## Main results

* `CategoryTheory.Subfunctor.exists_iso_preimage_ι_comm`: the two presentations of the
  intersection of two subfunctors are isomorphic over the ambient presheaf.
* `CategoryTheory.Subfunctor.exists_isPullback_preimage_preimage_ι`: the intersection of the
  inverse image of a subfunctor with the inverse image of another is a fibre product of the
  intersection of the two.
* `AlgebraicGeometry.Stack.isPullback_representingMap_restrictionInnerSquare_hom`: the square of
  representing algebraic spaces of `AlgebraicGeometry.Stack.restrictionInnerSquare` is cartesian,
  for an arbitrary morphism of algebraic spaces restricting the source.
* `AlgebraicGeometry.Stack.exists_isPullback_fibreSpaceProjection_restriction`: the fibre over a
  field-valued point of a restriction of the source is the base change of the fibre of the
  source, compatibly with the structure morphism to `Spec k`.
* `AlgebraicGeometry.Stack.exists_iso_fibreOverFieldPoint_zeroLocusOnOpen`:
  **the fibre comparison itself** — a representing algebraic space of the fibre of the Stacks
  06MD slice is the intersection of the zero locus of the pulled-back functions with `p⁻¹V`
  inside a representing algebraic space of the fibre of the chart, compatibly with the structure
  morphism to `Spec k`.
* `AlgebraicGeometry.Stack`
  `.exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal`:
  the unramifiedness clause of **Stacks 06N2** for the Stacks 06MD slice, with no comparison of
  fibres left owed — the three results above joined to the chart of
  `AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`
  and to
  `AlgebraicGeometry.Stack.exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt`.

## Implementation notes

The subspaces are taken as variables with their defining equations as hypotheses, so that the
proofs `subst` them and the two inverse-image presentations are compared once, abstractly, rather
than at the concrete zero loci. The closed subspace of `Fsp` is taken bundled, as an
`AlgebraicGeometry.Space.ClosedSubspaces`, because the chart lemma it is fed to reads its
representability datum `Z.2.2.rep` and a reconstructed bundling would not be the one the
hypotheses of that lemma are stated at.

No `@[stacks]` attribute is claimed. **Stacks 06N3** is no tag of its own: its registration sits
on `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.
**Stacks 083Q** is the inverse-image construction and its fibre-product characterisation, both
already tagged in `StacksFrontier/AlgebraicGeometry/Spaces/SubspacePreimage.lean`.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

universe u

/-- **The two presentations of the intersection of two subfunctors agree.** For subfunctors `A`
and `D` of a presheaf of types `X`, the inverse image of `A` along the inclusion of `D` and the
inverse image of `D` along the inclusion of `A` are isomorphic over `X`.

Both are fibre products of the cospan `(A.ι, D.ι)` by **Stacks 083Q**,
`CategoryTheory.Subfunctor.isPullback_preimage`, so the comparison is the uniqueness of a fibre
product; the compatibility over `X` is one of its two projections read through
`CategoryTheory.Subfunctor.fromPreimage_ι`. -/
theorem exists_iso_preimage_ι_comm {C : Type*} [Category C] {X : C ⥤ Type u} (A D : Subfunctor X) :
    ∃ e : (A.preimage D.ι).toFunctor ≅ (D.preimage A.ι).toFunctor,
      e.hom ≫ (D.preimage A.ι).ι ≫ A.ι = (A.preimage D.ι).ι ≫ D.ι := by
  refine ⟨(isPullback_preimage D.ι A).isoIsPullback _ _ (isPullback_preimage A.ι D).flip, ?_⟩
  rw [← Category.assoc, IsPullback.isoIsPullback_hom_fst]
  exact fromPreimage_ι A D.ι

/-- **The intersection of the inverse images of two subfunctors is a fibre product of their
intersection.** Let `q : Y ⟶ X` be a morphism of presheaves of types, let `A` and `D` be
subfunctors of `X`, let `Zc = q⁻¹D` and let `Gq = Zc ∩ q⁻¹A` be the inverse image of `q⁻¹A` in
`Zc`. Then `Gq` is a fibre product of `q` and of the inclusion into `X` of the intersection
`D ∩ A`, read as the inverse image of `D` along `A.ι`.

The inverse image is taken twice, so `Gq` is the inverse image of `A` along `Zc ⟶ D` — this is
`CategoryTheory.Subfunctor.preimage_comp` together with
`CategoryTheory.Subfunctor.fromPreimage_ι` — and pasting that fibre product square onto the one
exhibiting `Zc` as `q⁻¹D` gives the fibre product over `X` of `q` with `A ∩ D` in the
presentation `A.preimage D.ι`;
`CategoryTheory.Subfunctor.exists_iso_preimage_ι_comm` swaps that for the presentation
`D.preimage A.ι`. -/
theorem exists_isPullback_preimage_preimage_ι {C : Type*} [Category C] {X Y : C ⥤ Type u}
    (q : Y ⟶ X) (A D : Subfunctor X) (Zc : Subfunctor Y) (hZc : Zc = D.preimage q)
    (Gq : Subfunctor Zc.toFunctor) (hGq : Gq = (A.preimage q).preimage Zc.ι) :
    ∃ δ : Gq.toFunctor ⟶ (D.preimage A.ι).toFunctor,
      IsPullback (Gq.ι ≫ Zc.ι) δ q ((D.preimage A.ι).ι ≫ A.ι) := by
  subst hZc
  obtain rfl : Gq = (A.preimage D.ι).preimage (D.fromPreimage q) := by
    rw [hGq, ← preimage_comp, ← fromPreimage_ι, preimage_comp]
  obtain ⟨e, he⟩ := exists_iso_preimage_ι_comm A D
  exact ⟨(A.preimage D.ι).fromPreimage (D.fromPreimage q) ≫ e.hom,
    ((isPullback_preimage (D.fromPreimage q) (A.preimage D.ι)).flip.paste_horiz
      (isPullback_preimage q D).flip).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    (by simp) (by simp) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id]; exact he.symm)⟩

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Inner

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
  (ι : W ⟶ U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒳)
  (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 c).pt.val.val.p
    (presheafOfCategories (Q ⋙ typeToCat)).p)

/-- **The square of representing algebraic spaces of the inner square is cartesian, for an
arbitrary restriction of the source.** Let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space to
an algebraic stack over `S`, let `c : 𝒲 ⟶ 𝒳` be another 1-morphism and let `ι : W ⟶ U` be a
morphism of algebraic spaces. Then the square of representing algebraic spaces which
`AlgebraicGeometry.Stack.restrictionInnerSquare` induces through **Stacks 04SW** is cartesian,
its bottom edge being `ι` itself.

This is `AlgebraicGeometry.Stack.isPullback_representingMap_restrictionInnerSquare` with the
inclusion of a subfunctor of `U` replaced by an arbitrary morphism, proved the same way: the inner
square is the canonical 2-fibre product of the cospan `(U ×_𝒳 𝒲 ⟶ U, W ⟶ U)`, so
`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct` applies, and the
1-morphism of algebraic stacks attached to a morphism of algebraic spaces reads back as that
morphism by `AlgebraicGeometry.Stack.representingMap_associatedMap`.

The generality is what the Stacks 06MD slice needs: the slice reaches `U` through the composite
`Zsl.ι ≫ V.ι` of the inclusion of the zero locus into the open subspace with the inclusion of the
open subspace, and that composite is not the inclusion of a subfunctor of `U`, so the subfunctor
form does not reach the stack whose fibre has to be taken. -/
theorem isPullback_representingMap_restrictionInnerSquare_hom :
    IsPullback
      (representingMap B S hS
        (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 c).pt.val
        (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val Q P eQ eP
        (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 c).fst.hom)
      (representingMap B S hS
        (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 c).pt.val
        (algebraicSpaceStack.{u, w} B S hS W hW).val Q W eQ
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 c).snd.hom)
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom)
      ι := by
  convert isPullback_representingMap_of_isTwoFibreProduct B S hS
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι).hom)
    P W U Q Q eP (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eQ eQ using 1 <;>
    first | exact (representingMap_associatedMap B S hS W U ι).symm | rfl

end Inner

section Fibre

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)
  (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
  (ι : W ⟶ U)
  (Qq : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 W hW k hk toBase
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) g).val.val.p
    (presheafOfCategories (Qq ⋙ typeToCat)).p)

/-- **The fibre over a field-valued point of a restriction of the source is the base change of
the fibre of the source.** Let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space, let
`g : Spec k ⟶ 𝒳` be a field-valued point in the spelling of **Stacks 06PU**, let `Fsp` represent
the fibre `F = U ×_𝒳 Spec k` and let `ι : W ⟶ U` be a morphism of algebraic spaces. Then a
representing algebraic space `Qq` of the fibre `W ×_𝒳 Spec k` of the restricted 1-morphism
carries a morphism `κ : Qq ⟶ Fsp` which exhibits it as the base change of `Fsp` along `ι`, and
which carries the structure morphism of `Fsp` over `Spec k` to that of `Qq`.

`AlgebraicGeometry.Stack.isPullback_representingMap_restrictionInnerSquare_hom` is the statement
for the apex of `AlgebraicGeometry.Stack.restrictionSquare`, whose cospan is oriented
`(g, W ⟶ 𝒳)`, while the fibre `AlgebraicGeometry.Stack.fibreOverFieldPoint` is the canonical
2-fibre product of the reverse cospan; so the legs are exchanged once at each end, by
`AlgebraicGeometry.Stack.exists_isIso_representingMap_twoFibreProductSquare_swap` for `Fsp` and by
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct` for `Qq`, and the
cartesian square is transported along the two comparisons. The structure morphism is the
remaining projection of the same comparison, read through
`AlgebraicGeometry.Stack.representingMap_restrictionSquare_fst`, which splits the projection of
the restricted base change onto `Spec k` as the inner projection followed by that of `F`. -/
theorem exists_isPullback_fibreSpaceProjection_restriction :
    ∃ κ : Qq ⟶ Fsp,
      IsPullback κ
        (fibreSpaceProjection B S hS 𝒳 W hW k hk toBase
          (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) g Qq eQ)
        (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) ι ∧
      κ ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
        fibreSpaceStructureMorphism B S hS 𝒳 W hW k hk toBase
          (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) g Qq eQ := by
  classical
  obtain ⟨P, hP, ⟨eP⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val
      (algebraicSpaceStack.{u, w} B S hS U hU).val g.hom.hom f.hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
  obtain ⟨Q', hQ', ⟨eQ'⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
      (algebraicSpaceStack.{u, w} B S hS W hW).val
      (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι).hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS
        (algebraicSpaceStack.{u, w} B S hS U hU) W hW
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι))
      ⟨P, hP, ⟨eP⟩⟩
  have hsq := isPullback_representingMap_restrictionInnerSquare_hom.{u, w} B S hS 𝒳 U W hU hW ι f
    (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g P Q' eP eQ'
  obtain ⟨mP, hmP, hmP1, hmP2⟩ := exists_isIso_representingMap_twoFibreProductSquare_swap
    B S hS 𝒳 f g Fsp P U (yoneda.obj (fieldPointObject B S hS k hk toBase))
    eF eP (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
  obtain ⟨n, hn, hn1, hn2⟩ := exists_isIso_representingMap_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f).hom g.hom))
    (Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS g
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f))
      (isTwoFibreProduct_restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f).hom))
    Qq Q' (yoneda.obj (fieldPointObject B S hS k hk toBase)) W eQ eQ'
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have hmP1' : mP ≫ representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val P
        (yoneda.obj (fieldPointObject B S hS k hk toBase)) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom =
      fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF := hmP1
  refine ⟨n ≫ representingMap B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).pt.val
      (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val Q' P eQ' eP
      (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g).fst.hom ≫
    inv mP, ?_, ?_⟩
  · exact hsq.of_iso' (asIso n) (asIso mP) (Iso.refl _) (Iso.refl _) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hn2)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hmP2) (by simp)
  · rw [← hmP1']
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← representingMap_restrictionSquare_fst.{u, w} B S hS 𝒳 U W hU hW ι f
      (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)) g P Q' eP
      (yoneda.obj (fieldPointObject B S hS k hk toBase))
      (PresheafOfCategories.sliceElementsEquivalenceOver _) eQ']
    exact hn1

end Fibre

section Slice

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)
  {r : ℕ}
  (c : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)
  (V : Subfunctor U)
  (Zsl : Subfunctor V.toFunctor) (hZslsp : IsAlgebraicSpace B S hS Zsl.toFunctor)
  (hZsl : Zsl = zeroLocusOnOpen B S hS U hU c V)
  (Qq : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
      (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g).val.val.p
    (presheafOfCategories (Qq ⋙ typeToCat)).p)
  (Zcl : Subfunctor Fsp)
  (hZcl : Zcl = Space.vanishingSubfunctor B S hS ⟨Fsp, hFsp⟩
    (fun i => Space.globalFunctionsMap B S hS
      (ObjectProperty.homMk (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) (c i)))
  (O : Subfunctor Fsp)
  (hO : O = V.preimage (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF))
  (Gg : Subfunctor Zcl.toFunctor) (hGg : Gg = O.preimage Zcl.ι)

include hZsl hZcl hO hGg in
/-- **The fibre of the Stacks 06MD slice over the field point, read inside the fibre of the
chart.** Let `f : U ⟶ 𝒳` be a 1-morphism from an algebraic space, let `g : Spec k ⟶ 𝒳` be a
field-valued point, let `Fsp` represent the fibre `F = U ×_𝒳 Spec k` with projection
`p : Fsp ⟶ U`, let `c₁, …, c_r` be global regular functions on `U` and let `V ⊆ U` be a
subfunctor. Let `Zsl = V(c₁, …, c_r) ∩ V` be the slice of **Stacks 06MD** and let `Qq` represent
the fibre `Zsl ×_𝒳 Spec k`, the slice reaching `𝒳` through `Zsl.ι ≫ V.ι` followed by `f`. Then
`Qq` is isomorphic to the intersection inside `Fsp` of the zero locus
`Zcl = V(p^*c₁, …, p^*c_r)` of the pulled-back functions with the inverse image `p⁻¹V`,
compatibly with the structure morphism to `Spec k`.

This is the identification the chart construction of **Stacks 06N3** needs: the unramifiedness
clause of **Stacks 06N2** is a condition on the fibre of the slice, while the étale chart at
which it is checked is produced inside `Zcl ∩ p⁻¹V`, on the affine étale chart of `Fsp` which the
slicing sequence and the closed point of **Stacks 056U** already live on.

The fibre of the slice is the base change along `Zsl.ι ≫ V.ι` of the fibre of the chart, by
`AlgebraicGeometry.Stack.exists_isPullback_fibreSpaceProjection_restriction`; the zero locus of
the pulled-back functions is the inverse image of `V(c₁, …, c_r)` along `p`
(`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`, which needs no
hypothesis on `p`), so `Zcl ∩ p⁻¹V` is also such a base change by
`CategoryTheory.Subfunctor.exists_isPullback_preimage_preimage_ι`, and two fibre products of one
cospan are uniquely isomorphic. The compatibility with the structure morphism is the one the
first of those two results carries. No closedness of the slice and no openness of `V` is
used. -/
theorem exists_iso_fibreOverFieldPoint_zeroLocusOnOpen :
    ∃ ε : Qq ≅ Gg.toFunctor,
      ε.hom ≫ Gg.ι ≫ Zcl.ι ≫
          fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
        fibreSpaceStructureMorphism B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
          (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g Qq eQ := by
  classical
  obtain rfl : Zsl = (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ c).preimage V.ι := hZsl
  obtain ⟨κ, hκ, hκσ⟩ := exists_isPullback_fibreSpaceProjection_restriction.{u, w} B S hS 𝒳 U hU
    k hk toBase f g Fsp eF
    ((Space.vanishingSubfunctor B S hS ⟨U, hU⟩ c).preimage V.ι).toFunctor hZslsp
    (((Space.vanishingSubfunctor B S hS ⟨U, hU⟩ c).preimage V.ι).ι ≫ V.ι) Qq eQ
  obtain ⟨δ, hδ⟩ := Subfunctor.exists_isPullback_preimage_preimage_ι
    (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) V
    (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ c) Zcl
    (hZcl.trans (Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage B S hS
      (ObjectProperty.homMk (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) c))
    Gg (hGg.trans (by rw [hO]))
  refine ⟨hκ.isoIsPullback _ _ hδ, ?_⟩
  rw [reassoc_of% (IsPullback.isoIsPullback_hom_fst _ _ hκ hδ)]
  exact hκσ

end Slice

section Assembly

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)
  {r : ℕ}
  (c : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)
  (V : Subfunctor U)
  (Zsl : Subfunctor V.toFunctor) (hZslsp : IsAlgebraicSpace B S hS Zsl.toFunctor)
  (hZsl : Zsl = zeroLocusOnOpen B S hS U hU c V)
  (Qq : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hQq : IsAlgebraicSpace B S hS Qq)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
      (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g).val.val.p
    (presheafOfCategories (Qq ⋙ typeToCat)).p)
  (Zc : Space.ClosedSubspaces B S hS Fsp)
  (hZc : Zc.1 = Space.vanishingSubfunctor B S hS ⟨Fsp, hFsp⟩
    (fun i => Space.globalFunctionsMap B S hS
      (ObjectProperty.homMk (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩) (c i)))
  (Wc : Space.SmallEtale B S hS Fsp)
  (β : Wc.obj.left ⟶ fieldPointObject B S hS k hk toBase)
  (hβ : Wc.obj.hom ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
    yoneda.map β)

include hQq hZsl hZc hβ in
/-- **The unramifiedness clause of Stacks 06N2 for the Stacks 06MD slice, with no comparison of
fibres left owed.** At the configuration of the chart construction of **Stacks 06N3** — `Fsp`
representing the fibre `F = U ×_𝒳 Spec k` of the chart, `Zc` the closed subspace
`V(p^*c₁, …, p^*c_r) ⊆ Fsp`, `Wc` an affine étale chart of `Fsp` with `β : Wc ⟶ Spec k` under the
structure morphism, `w` a point of its scheme at which no section of the defining ideal of `Zc`
is invertible and whose point of `|Fsp|` lies in `p⁻¹V`, and the morphism of schemes
`Zc ×_{Fsp} Wc ⟶ Spec k` unramified at every point over `w` — the condition
`AlgebraicGeometry.Stack.FibreIsUnramifiedNear` of **Stacks 06N2** holds for the slice
`Zsl = V(c₁, …, c_r) ∩ V` at a point of `|Qq|`, where `Qq` represents the fibre
`Zsl ×_𝒳 Spec k`.

This is
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`,
which produces the étale chart of `Zc ∩ p⁻¹V` and the point at which the morphism of schemes to
`Spec k` is unramified, fed to
`AlgebraicGeometry.Stack.exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt` along the
identification of fibres
`AlgebraicGeometry.Stack.exists_iso_fibreOverFieldPoint_zeroLocusOnOpen`.
Nothing else is owed by the unramifiedness half of the chart at a finite type point: the three
geometric inputs are the slicing sequence's germ clause, the criterion of **Stacks 02GF** on the
chart and the point-set conclusion of **Stacks 06MD**, and all three are stated here exactly as
those results deliver them. -/
theorem exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal
    (hWc : IsAffine (Space.chartScheme Wc))
    (I : Ideal Γ(Space.chartScheme Wc, ⊤))
    (hI : Space.definingIdealAt B S hS ⟨Fsp, hFsp⟩ Zc (Opposite.op Wc) = I)
    (w : Space.chartScheme Wc)
    (hgerm : ∀ s ∈ I, (Space.chartScheme Wc).presheaf.germ ⊤ w trivial s ∈
      IsLocalRing.maximalIdeal ((Space.chartScheme Wc).presheaf.stalk w))
    (hunr : ∀ z : (BigFppfOver.toScheme B S hS).obj (Zc.2.2.rep.pullback Wc.1.hom),
      Space.chartBaseChangeHom B S hS ⟨Fsp, hFsp⟩ Zc Wc z = w →
        _root_.AlgebraicGeometry.UnramifiedAt
          ((BigFppfOver.toScheme B S hS).map (Zc.2.2.rep.snd Wc.1.hom ≫ β)) z)
    (O : Subfunctor Fsp) (hO : Space.IsOpenSubspace B S hS O)
    (hOV : O = V.preimage (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF))
    (hw : Space.pointsMap B S hS
        (yoneda.obj ((Space.SmallEtale.toOver B S hS Fsp).obj Wc)) Wc.1.hom
        ((Space.pointsEquivScheme B S hS ((Space.SmallEtale.toOver B S hS Fsp).obj Wc)).symm w) ∈
      Set.range (Space.pointsMap B S hS O.toFunctor O.ι)) :
    ∃ xF : Space.points B S hS Qq,
      FibreIsUnramifiedNear.{u, w} B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
        (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g
        (spacePointMap B S hS Qq
          (fibreOverFieldPoint B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
            (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g).val
          (representingEquivalence B S hS Qq
            (fibreOverFieldPoint B S hS 𝒳 Zsl.toFunctor hZslsp k hk toBase
              (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g).val
            eQ).functor xF) := by
  classical
  obtain ⟨ε, hε⟩ :=
    exists_iso_fibreOverFieldPoint_zeroLocusOnOpen.{u, w}
      B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF c V Zsl hZslsp hZsl Qq eQ Zc.1 hZc O hOV
      (O.preimage Zc.1.ι) rfl
  obtain ⟨A, a, h, hAaff, haEt, hfac, v, hv⟩ :=
    Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal.{u}
      B S hS ⟨Fsp, hFsp⟩ Zc (isAlgebraicSpace_yoneda B S hS (fieldPointObject B S hS k hk toBase))
      (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) Wc β hβ hWc I hI w
      hgerm hunr O hO hw (O.preimage Zc.1.ι) rfl
  exact exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt.{u, w} B S hS 𝒳
    Zsl.toFunctor hZslsp k hk toBase
    (algebraicSpaceStackMap.{u, w} B S hS hZslsp hU (Zsl.ι ≫ V.ι) ≫ f) g Qq hQq eQ ε
    ((O.preimage Zc.1.ι).ι ≫ Zc.1.ι ≫
      fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) hε a haEt h hfac v hv

end Assembly

end AlgebraicGeometry.Stack

end

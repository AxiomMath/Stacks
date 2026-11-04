module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections

/-!
# The étale-smooth property of a base change of the top morphism (Stacks 0CG1, 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target in the sense of **Stacks 0CFZ**, let `hTop : U ⟶ V` have `P`, let
`s : 𝒮 ⟶ V` be a smooth 1-morphism out of a category fibred in groupoids over the big fppf site
of `S`, and form the canonical 2-fibre product `𝒮 ×_V U`. This module proves that every *étale*
morphism of algebraic spaces into the representing presheaf of that 2-fibre product, composed
with the morphism induced by its projection to `𝒮`, has `P`.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp_etale`: the statement
  above.

## Implementation notes

This is the étale-smooth analogue of
`AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp`, and it is the single step
at which `P` is used in the étale-smooth diagram criterion of **Stacks 0CIF**: the base change of
the given diagram's top morphism along the smooth 1-morphism `s` has `P`, and the comparison from
the apex of the arbitrary diagram into it is étale.

The two statements differ in three ways, and all three are forced by the vocabulary Stacks 0CIF
is written at rather than chosen. First, `P` is a property of morphisms of the category
`AlgebraicGeometry.AlgebraicSpaces` of **Stacks 02X2**, not of morphisms of presheaves, so
algebraicity is carried by the objects. Second, the comparison is étale rather than smooth.
Third, and this is what makes the proof shorter than its smooth analogue, no seven-term
equivalence has to be instantiated: the two fields
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget.pullbackSnd_of_smooth` and
`…precomp_of_etale` of **Stacks 0CFZ** are exactly the two steps, where the smooth analogue has
to go through criterion (4) of Stacks 06FA. In other words this is
`AlgebraicGeometry.Space.prop_etale_smooth_diagram_of_prop` — Stacks 0CG1, (a) ⇒ (d) — read
through **Stacks 04SD**.

Stacks 04SD is what identifies the representing presheaf of `𝒮 ×_V U` with the fibre product of
the representing presheaves compatibly with the projections
(`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` and
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_fst`), so that the
projection to `𝒮` becomes the pullback projection of `hTop` along the smooth morphism induced by
`s`. The comparison isomorphism is used in its `.hom` direction throughout, because
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` is noncomputable and its `.inv` does not
reduce.

No `@[stacks]` attribute: neither 0CG1 nor 0CIF is covered by this statement alone — 0CG1's
covering set is the seven conditions it compares, already carried by
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothDiagram`, and 0CIF's is its three comparison
theorems.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The single step at which `P` is used in the étale-smooth diagram criterion of
Stacks 0CIF.** Let `P` be étale-smooth local on the source-and-target, let `hTop : U ⟶ V` have
`P`, let `s : 𝒮 ⟶ V` be a smooth 1-morphism out of a category fibred in groupoids over the big
fppf site of `S`, and form the canonical 2-fibre product `𝒮 ×_V U`. Then every étale morphism of
algebraic spaces into the representing presheaf of that 2-fibre product, composed with the
morphism induced by its projection to `𝒮`, has `P`.

This is `AlgebraicGeometry.Space.prop_etale_smooth_diagram_of_prop` (**Stacks 0CG1**, (a) ⇒ (d))
read through **Stacks 04SD**: the projection to `𝒮` becomes the pullback projection of `hTop`
along the smooth morphism of algebraic spaces induced by `s`, which has `P` by smooth base
change, and precomposing with an étale morphism preserves `P`. -/
theorem prop_representingMap_twoFibreProductFst_comp_etale
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hTop : U ⟶ V)
    (hPtop : P (ObjectProperty.homMk hTop : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩))
    {𝒮 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (s : 𝒮 ⟶ fibredCategory B S hS V) (hs : IsRelativelySmooth B S hS s)
    (W₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₃ : IsAlgebraicSpace B S hS W₃)
    (eW₃ : StacksRepresentableCFG.EquivalenceOver 𝒮.val.p
      (presheafOfCategories (W₃ ⋙ typeToCat)).p)
    (W₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hW₂ : IsAlgebraicSpace B S hS W₂)
    (eW₂ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
        (fibredCategory B S hS V) s (associatedMap B S hS hTop).1)
      (presheafOfCategories (W₂ ⋙ typeToCat)).p)
    {WE : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hWE : IsAlgebraicSpace B S hS WE)
    (q : WE ⟶ W₂) (hq : Space.IsEtale B S hS q) :
    P (ObjectProperty.homMk (q ≫ representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).fst) :
      (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₃, hW₃⟩) := by
  let β := representingMap B S hS 𝒮 (fibredCategory B S hS V) W₃ V eW₃
    (StacksRepresentableCFG.EquivalenceOver.refl _) s
  let hTopR := representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS hTop).1
  have hPtopR : P (ObjectProperty.homMk hTopR :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) := by
    rwa [show hTopR = hTop from representingMap_associatedMap B S hS U V hTop]
  -- Stacks 04SD: the representing presheaf of the 2-fibre product is the fibre product
  let _hfibered : (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
      (fibredCategory B S hS V) s (associatedMap B S hS hTop).1).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
      (associatedMap B S hS hTop).1).pt.property.isFibered
  let hfib : Presheaf.fibreProduct β hTopR ≅ W₂ :=
    fibreProductIsoRepresenting B S hS 𝒮 (fibredCategory B S hS U) (fibredCategory B S hS V)
      W₃ U V eW₃ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  have hfst : hfib.hom ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst =
      Presheaf.fibreProductFst β hTopR :=
    fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS 𝒮
      (fibredCategory B S hS U) (fibredCategory B S hS V) W₃ U V eW₃
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  -- and therefore the pullback of `hTop` along the smooth morphism induced by `s`
  let ι := hfib.symm ≪≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback
  have hgoal : (q ≫ ι.hom) ≫ pullback.snd hTopR β =
      q ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst := by
    have hιhom : ι.hom =
        hfib.inv ≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback.hom := rfl
    rw [hιhom, Category.assoc, Category.assoc,
      (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback_hom_snd, ← hfst,
      Iso.inv_hom_id_assoc]
  have hβsm : Space.IsSmooth B S hS β :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS s hs.1 W₃ V hW₃ hV eW₃
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hs
  -- the two fields of Stacks 0CFZ: smooth base change, then étale precomposition
  let fU : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩ := ObjectProperty.homMk hTopR
  let fV : (⟨W₃, hW₃⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩ := ObjectProperty.homMk β
  have hpre := hP.precomp_of_etale
    (ObjectProperty.homMk (q ≫ ι.hom) :
      (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ AlgebraicSpaces.fiberProduct B S hS fU fV)
    (ObjectProperty.homMk (pullback.snd fU.hom fV.hom) :
      AlgebraicSpaces.fiberProduct B S hS fU fV ⟶ ⟨W₃, hW₃⟩)
    (Space.isEtale_comp B S hS hq (Space.isEtale_of_isIso B S hS ι.hom))
    (hP.pullbackSnd_of_smooth fU hPtopR fV hβsm)
  exact hgoal ▸ hpre

end AlgebraicGeometry.Stack

end

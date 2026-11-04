module

public import StacksFrontier.AlgebraicGeometry.Quot.BaseBasedCategoryElements
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicCoverLargeHoms
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory

/-!
# Stacks 0DLN, the reduction to a base which is a scheme

The second paragraph of the proof of Stacks 0DLN reduces the general case to the case where the
base `B` is a scheme. Choose a scheme `B'` and a surjective étale morphism `B' ⟶ B`, and set
`X' = B' ×_B X`. By Remark 0DLI, `Complexes_{X'/B'}` is the 2-fibre product of `Complexes_{X/B}`
with `𝒮_{B'}` over `𝒮_B`. By the material of Section 03YJ the projection
`Complexes_{X'/B'} ⟶ Complexes_{X/B}` is therefore surjective and étale, and algebraicity
descends along it.

This file carries out that paragraph. Remark 0DLI and Lemmas 0DLF, 0DLG and 0DLH are explicit
hypotheses stated at their Stacks content. The rest is proved:

* the base-changed situation `X' ⟶ B'` is again proper, flat and of finite presentation;
* `𝒮_{B'} ⟶ 𝒮_B` is representable by algebraic spaces, surjective and étale, by Stacks 045A
  (`AlgebraicGeometry.Space.prop_baseBasedMap_schemeSpace`);
* the projection of the 2-fibre product is representable, surjective and étale, by Stacks 0302
  and Stacks 045C;
* algebraicity descends along it
  (`AlgebraicGeometry.Stack.isAlgebraicStack_of_etaleSurjectiveCoverLargeHoms`).

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.baseChange`: the situation of Stacks 0DLE base
  changed along a morphism `Y' ⟶ Y` of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_isAlgebraicStack_schemeBase`:
  if `Complexes_{X/B}` is an algebraic stack for every situation whose base is a scheme, then it
  is one for every situation over `S`.

## Implementation notes

The hypothesis `h0DLI` asks for the square of Remark 0DLI in the shape of the square of Stacks
08LP (`AlgebraicGeometry.Space.CoherentSituation.baseChangeSquare'`): a 2-commutative square
over `(q, 𝒮_{B'} ⟶ 𝒮_B)` in the 2-category of categories over the site, with apex
`Complexes_{X'/B'}`, which is a 2-fibre product. Its two 1-morphisms out of `Complexes_{X'/B'}` and
the 1-morphism `q` to `𝒮_B` are existentially quantified, so the hypothesis follows from Remark
0DLI, which names them.

The hypothesis `h0DLH` is the stack condition of Stacks 0DLH for the fppf topology, in the
family-indexed form `CategoryTheory.Functor.IsStackInGroupoids` at the index universe `u + 1`. The
sieve-indexed form follows from it by `CategoryTheory.Functor.isStack_of_isStackInGroupoids`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 03YJ](https://stacks.math.columbia.edu/tag/03YJ)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- **The base change of the situation of Stacks 0DLE.** For a morphism `g : Y' ⟶ Y` of
algebraic spaces the projection `f' : X ×_Y Y' ⟶ Y'` is again proper, flat and of finite
presentation, each property being stable under base change (Stacks 03ZM, 03MO, 03XR). -/
def baseChange (D : ComplexesSituation B S hS) {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y) :
    ComplexesSituation B S hS where
  toCoherentSituation := D.toCoherentSituation.baseChange g
  proper :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsProper B S hS k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f g) D.proper
  flat :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f g) D.flat

/-- The base of the base-changed situation is the new base. -/
theorem baseChange_Y (D : ComplexesSituation B S hS) {Y' : AlgebraicSpaces B S hS}
    (g : Y' ⟶ D.Y) : (D.baseChange g).Y = Y' :=
  rfl

/-- **Stacks 0DLN, the reduction to a base which is a scheme** (the second paragraph of the
source's proof). Assume Lemmas 0DLF, 0DLG and 0DLH and Remark 0DLI for every situation over `S`.
If `Complexes_{X/B}` is an algebraic stack whenever the base `B` is a scheme, then it is an
algebraic stack for every situation over `S`.

The hypotheses are:

* `h0DLF`: Stacks 0DLF, `p : Complexes_{X/B} ⟶ (Sch/S)_fppf` is fibred in groupoids;
* `h0DLG`: Stacks 0DLG, the diagonal of `Complexes_{X/B}` is representable by algebraic spaces;
* `h0DLH`: Stacks 0DLH, `Complexes_{X/B}` is a stack in groupoids for the fppf topology;
* `h0DLI`: Remark 0DLI, for `g : B' ⟶ B` the square with apex `Complexes_{X'/B'}` over
  `Complexes_{X/B} ⟶ 𝒮_B ⟵ 𝒮_{B'}` is a 2-fibre product;
* `hscheme`: the case of a base which is a scheme.

Choose a surjective étale atlas `B' ⟶ B` by a scheme (Stacks 025Y). The 1-morphism
`𝒮_{B'} ⟶ 𝒮_B` is representable, surjective and étale (Stacks 045A), so is its base change
`Complexes_{X'/B'} ⟶ Complexes_{X/B}` (Stacks 0302, 045C), and `Complexes_{X'/B'}` is algebraic by
`hscheme`. -/
theorem isAlgebraicStack_of_isAlgebraicStack_schemeBase
    (h0DLF : ∀ D : ComplexesSituation B S hS, (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ D : ComplexesSituation B S hS, Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF D)))
    (h0DLH : ∀ D : ComplexesSituation B S hS,
      (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS))
    (h0DLI : ∀ (D : ComplexesSituation B S hS) {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hscheme : ∀ D : ComplexesSituation B S hS,
      (∃ T : BigFppfOver B S hS, Nonempty (D.Y ≅ (schemeSpaceFunctor B S hS).obj T)) →
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D))
    (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) := by
  -- a surjective étale atlas of the base by a scheme
  obtain ⟨T, a, hsurjp, hetalep⟩ := D.Y.2.exists_atlas
  let g : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y := ObjectProperty.homMk a
  have hgsurj : Space.surjectiveMorphismProperty B S hS g :=
    (Space.surjective_iff_surjective_pointsMap B S hS D.Y.obj D.Y.2 T a).1 hsurjp
  have hgetale : Space.etaleMorphisms B S hS g :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 hetalep
  -- the square of Remark 0DLI, read in the 2-category of categories fibred in groupoids
  obtain ⟨q, t, q', e, ⟨hR⟩⟩ := h0DLI D g
  let 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF D)
  let 𝒳' : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory (D.baseChange g)) (h0DLF (D.baseChange g))
  let qC : 𝒳 ⟶ baseFibredCategory D.Y := Bicategory.InducedBicategory.mkHom q
  let P : Bicategory.TwoCommSq qC (baseFibredMap D.Y g) :=
    { pt := 𝒳'
      fst := Bicategory.InducedBicategory.mkHom t
      snd := Bicategory.InducedBicategory.mkHom q'
      iso := Bicategory.InducedBicategory.isoMk e }
  have hP : Bicategory.IsTwoFibreProduct P := Bicategory.isTwoFibreProduct_of_underlying hR
  -- `𝒮_{B'} ⟶ 𝒮_B` is representable, surjective and étale
  have hf : Stack.IsRepresentableByAlgebraicSpaces B S hS (baseFibredMap D.Y g).hom :=
    isRepresentableByAlgebraicSpaces_baseBasedMap_schemeSpace g
  -- so is its base change `Complexes_{X'/B'} ⟶ Complexes_{X/B}`
  have hrep := Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} B S hS
    (baseFibredCategory _) (baseFibredCategory D.Y) 𝒳 (baseFibredMap D.Y g) qC P hP hf
  have hbc (Q : MorphismProperty (AlgebraicSpaces B S hS)) [Q.IsStableUnderBaseChange]
      [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)] (hg : Q g) :
      Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS Q P.fst hrep :=
    Stack.hasRelativeProperty_baseChange.{u, u + 1, u + 1, u} B S hS Q (baseFibredCategory _)
      (baseFibredCategory D.Y) 𝒳 (baseFibredMap D.Y g) qC P hP hf
      (prop_baseBasedMap_schemeSpace g Q hg)
  -- algebraicity descends along it
  have : 𝒳.val.p.IsFibered := (h0DLF D).isFibered
  exact Stack.isAlgebraicStack_of_etaleSurjectiveCoverLargeHoms.{u, u + 1, u, z} B S hS
    (𝒲 := 𝒳') (𝒴 := 𝒳) P.fst
    (hscheme (D.baseChange g) ⟨T, ⟨Iso.refl _⟩⟩)
    (Functor.isStack_of_isStackInGroupoids (h0DLH D)) (h0DLG D) hrep (hbc _ hgsurj) (hbc _ hgetale)

end AlgebraicGeometry.Space.ComplexesSituation

end

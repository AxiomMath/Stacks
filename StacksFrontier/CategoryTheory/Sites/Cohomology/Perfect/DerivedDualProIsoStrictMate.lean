module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualProIsoDualComplexMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexOfModules

/-!
# The mate for the dual complex of Tag 0FPR is the induced map of dual complexes

`CochainComplex.mate_exactPairingDualComplex` says this in a general monoidal preadditive
category. This file reads it at the dual complex `𝒢^• = 𝑆heafHom^•(ℱ^•, 𝒪)` of
[Stacks, Tag 0FPR] and the pairing `Stacks.SheafOfModules.Strict.exactPairingDualComplex`, which
is the shape its consumers use.

## Main results

* `Stacks.SheafOfModules.Strict.dualComplexMap`: the morphism `𝒢'^• ⟶ 𝒢^•` of dual complexes of
  [Stacks, Tag 0FPR] induced by a chain map `φ : ℱ^• ⟶ ℱ'^•` — the functoriality the dual
  complex of the tag did not have.
* `Stacks.SheafOfModules.Strict.mate_exactPairingDualComplex`: **the mate of `φ : ℱ^• ⟶ ℱ'^•`
  for the pairings of [Stacks, Tag 0FPR] is that morphism.**

## Implementation notes

**Why this is a file of its own.** `Mod(𝒪)` carries two monoidal structures with the same tensor
product, and the monoidal structure on complexes that the pairing of [Stacks, Tag 0FPR] is stated
over is built from the strict one by `Stacks.SheafOfModules.Strict.monoidalCategoryCochainComplex`.
The general lemma must therefore be applied with the strict structure, and its auxiliary data
supplied exactly as `Stacks.SheafOfModules.Strict.exactPairingDualComplex` supplies it — the same
`letI` block, so that the two readings of the pairing are the same term. Nothing here brings the
re-seated structure of [Stacks, Tag 0FPT] into scope, and a single `MonoidalCategory (Mod 𝒪)`
query in this file can only be answered one way.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (F : CochainComplex (Mod R) ℤ)
  (hF : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (F.X n))

/-- **The morphism of dual complexes of [Stacks, Tag 0FPR] induced by a chain map.** A chain map
`φ : ℱ^• ⟶ ℱ'^•` induces `𝒢'^• ⟶ 𝒢^•` in the opposite direction, degreewise the mate of
`φ^{-j}` for the degreewise pairings of [Stacks, Tag 0FNY]. This is
`CochainComplex.dualComplexMap` read at the dual complex of the tag, where it needs no monoidal
structure to be in scope: the source and target are complexes and the map is a chain map. -/
def dualComplexMap (F' : CochainComplex (Mod R) ℤ)
    (hF' : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (F'.X n))
    (φ : F ⟶ F') : dualComplex R F' hF' ⟶ dualComplex R F hF :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  CochainComplex.dualComplexMap F (dualComplexX R F) (dualComplexPairing R F hF)
    F' (dualComplexX R F') (dualComplexPairing R F' hF') φ

omit [HasSheafify J AddCommGrpCat.{max u v}] in
/-- **The mate of a chain map for the pairings of [Stacks, Tag 0FPR] is the induced morphism of
dual complexes.** For `φ : ℱ^• ⟶ ℱ'^•` with both complexes termwise locally direct summands of
finite free modules and of bounded support, the mate `𝒢'^• ⟶ 𝒢^•` of `φ` in the monoidal
category of complexes of [Stacks, Tag 0FPQ] is
`Stacks.SheafOfModules.Strict.dualComplexMap`, whose degree-`j` component is the mate of
`φ^{-j}` for the degreewise pairings of [Stacks, Tag 0FNY]. -/
theorem mate_exactPairingDualComplex (s : Finset ℤ) (hb : ∀ m, m ∉ s → IsZero (F.X m))
    (F' : CochainComplex (Mod R) ℤ)
    (hF' : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (F'.X n))
    (s' : Finset ℤ) (hb' : ∀ m, m ∉ s' → IsZero (F'.X m)) (φ : F ⟶ F') :
    @ExactPairing.mate (CochainComplex (Mod R) ℤ) _ (monoidalCategoryCochainComplex R)
        F F' (dualComplex R F hF) (dualComplex R F' hF')
        (exactPairingDualComplex R F hF s hb) (exactPairingDualComplex R F' hF' s' hb') φ =
      dualComplexMap R F hF F' hF' φ := by
  let : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  exact CochainComplex.mate_exactPairingDualComplex F (dualComplexX R F)
    (dualComplexPairing R F hF) F' (dualComplexX R F') (dualComplexPairing R F' hF') φ s hb s' hb'

end Stacks.SheafOfModules.Strict

end

end

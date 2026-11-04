module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualShortExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankTensor

/-!
# Tensoring with a finite locally free module on a space is exact

Let `F` be an algebraic space over a scheme `S` and `ℳ` a finite locally free `𝒪_F`-module on the
small étale site. Tensoring with `ℳ`, on either side, carries short exact sequences of
`𝒪_F`-modules to short exact sequences: `ℳ` has a dual (Stacks 0FNY), so tensoring with it has
adjoints on both sides. This is the exactness used in the proof of Stacks 0ESE to tensor a
filtration with invertible successive quotients by a second module.

## Main results

* `AlgebraicGeometry.Space.shortExact_map_tensorRight` and
  `AlgebraicGeometry.Space.shortExact_map_tensorLeft`: **tensoring a short exact sequence with a
  finite locally free `𝒪_F`-module, on the right or on the left, gives a short exact sequence.**
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_tensorObj`: the tensor product of modules of
  ranks `r` and `s` has rank `r s`.

## References

* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed modulesMonoidalPreadditive

/-- A functor with adjoints on both sides sends short exact sequences to short exact sequences. -/
private theorem shortExact_map_of_adjunctions {C : Type*} [Category C] [Abelian C]
    {T L R : C ⥤ C} [T.PreservesZeroMorphisms] (adjL : L ⊣ T) (adjR : T ⊣ R)
    {S' : ShortComplex C} (hS' : S'.ShortExact) :
    (S'.map T).ShortExact := by
  have : PreservesFiniteColimits T :=
    adjR.leftAdjoint_preservesColimits.preservesFiniteColimits.{0, 0}
  have : PreservesFiniteLimits T := adjL.rightAdjoint_preservesLimits.preservesFiniteLimits.{0, 0}
  exact hS'.map_of_exact T

/-- **Tensoring on the right with a finite locally free `𝒪_F`-module is exact.** -/
theorem shortExact_map_tensorRight {S' : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hS' : S'.ShortExact) (M : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    (S'.map (tensorRight M)).ShortExact := by
  let : SymmetricCategory (Modules.{u, u} B S hS F hF) :=
    RingedSite.modulesSymmetric (smallEtaleRingedSite B S hS F hF)
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS F hF M hM
  let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
  exact shortExact_map_of_adjunctions (tensorRightAdjunction Mᘁ M) (tensorRightAdjunction M Mᘁ) hS'

/-- **Tensoring on the left with a finite locally free `𝒪_F`-module is exact.** -/
theorem shortExact_map_tensorLeft {S' : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hS' : S'.ShortExact) (M : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    (S'.map (tensorLeft M)).ShortExact := by
  let := hasRightDual_of_isFiniteLocallyFreeOnSite B S hS F hF M hM
  exact shortExact_map_of_adjunctions (tensorLeftAdjunction M Mᘁ) (ihom.adjunction M) hS'

/-- **The tensor product of finite locally free `𝒪_F`-modules of ranks `r` and `s` has rank
`r s`.** -/
theorem isFiniteLocallyFreeOfRank_tensorObj {M N : Modules.{u, u} B S hS F hF} {r s : ℕ}
    (hM : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) M r)
    (hN : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) N s) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) (M ⊗ N) (r * s) :=
  let _ := (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ (modulesTensorObjIso B S hS F hF M N).symm
    (RingedSite.isFiniteLocallyFreeOfRank_sheafTensor _ hM hN)

end AlgebraicGeometry.Space

end

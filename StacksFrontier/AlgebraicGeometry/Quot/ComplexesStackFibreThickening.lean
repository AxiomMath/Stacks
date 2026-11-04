module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingAffineSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocalFirstOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# The first-order thickening `X₀ ⊂ X_ε` of base changes (towards Stacks 0DLL)

In the proof of Stacks 0DLL, `X₀ = Spec(k) ×_B X` and `X_ε = Spec(k[ε]) ×_B X`, and "`X_ε` is a
first order thickening of `X₀` flat over the first order thickening `Spec(k) ⟶ Spec(k[ε])`".
This file proves the thickening half of that sentence in the generality in which it holds:
for any morphism `f : X ⟶ Y` of algebraic spaces and any morphism `h : T ⟶ T'` of test schemes
over `Y` which is a closed immersion with square-zero ideal, the induced morphism
`X_T ⟶ X_{T'}` of base changes is a first-order thickening of algebraic spaces.  Flatness of
`X_{T'}` over `T'` is `AlgebraicGeometry.Space.ComplexesSituation.projection_isFlat`.

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.isFirstOrderThickeningHom_schemeSpaceFunctor_map`: a square-zero
  closed immersion of schemes of the site represents a first-order thickening of algebraic
  spaces.
* `AlgebraicGeometry.Space.CoherentSituation.isFirstOrderThickeningHom_relativeMap`: its base
  change `X_h : X_T ⟶ X_{T'}` is a first-order thickening.
* `AlgebraicGeometry.Space.isLocallySurjective_fSharp_of_isThickening` and
  `AlgebraicGeometry.Space.fSharp_mul_eq_zero_of_isFirstOrderThickening`: for a first-order
  thickening `G ⊂ X`, the structure map `𝒪_X ⟶ i_*𝒪_G` of the small étale ringed topoi is a
  locally surjective map of sheaves of commutative rings on the site of `X` with square-zero
  kernel.  These are the hypotheses `hf` and `hsq` of the lifts of Stacks 0DIZ
  (`Deformation.ComplexLift.exists_addTorsor_squareZeroLifts`), on the site of `X`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A square-zero closed immersion of schemes of the site is a first-order thickening of
algebraic spaces.**  If the underlying morphism of schemes of `i : T ⟶ T'` is a closed
immersion whose ideal sheaf has square zero, then the induced morphism of the algebraic spaces
represented by `T` and `T'` identifies the first with a first-order thickening subspace of the
second (Stacks 05ZK, part (2)). -/
theorem isFirstOrderThickeningHom_schemeSpaceFunctor_map {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) :
    IsFirstOrderThickeningHom B S hS ((schemeSpaceFunctor B S hS).map i) := by
  have : Mono (yoneda.map i) := mono_yoneda_map_of_isClosedImmersion i hi.1
  exact ⟨inferInstanceAs (IsIso (Subfunctor.toRange (yoneda.map i))),
    isFirstOrderThickening_range_yoneda_map B S hS i hi⟩

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- **The base change of a first-order thickening of test schemes is a first-order thickening.**
Let `h : T ⟶ T'` be a morphism of test schemes over `Y` whose underlying morphism of schemes is
a closed immersion with square-zero ideal (for instance `Spec k ⟶ Spec k[ε]`).  Then the induced
morphism `X_h : X_T ⟶ X_{T'}` of base changes is a first-order thickening of algebraic spaces:
it is the base change of `T ⟶ T'` along `X_{T'} ⟶ T'` (Stacks 09ZX). -/
theorem isFirstOrderThickeningHom_relativeMap {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS h.left) :
    IsFirstOrderThickeningHom B S hS (D.relativeMap h) :=
  IsFirstOrderThickeningHom.of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f h)).flip
    (isFirstOrderThickeningHom_schemeSpaceFunctor_map h.left hi)

end CoherentSituation

/-! ### The square-zero structure map of a first-order thickening -/

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **The structure map of a thickening is locally surjective.**  For a thickening `G ⊂ X` of
algebraic spaces, the structure map `𝒪_X ⟶ i_*𝒪_G` of the morphism of small étale ringed topoi
of the inclusion is a locally surjective map of sheaves of commutative rings on the small étale
site of `X` (Stacks 03MB, through `AlgebraicGeometry.Space.isLocallySurjective_fSharp`). -/
theorem isLocallySurjective_fSharp_of_isThickening (hG : IsThickening B S hS X G) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk G.ι : hG.subspace ⟶ X)).fSharp.hom :=
  isLocallySurjective_fSharp B S hS _ hG.1.2

/-- **The kernel of the structure map of a first-order thickening has square zero.**  For a
first-order thickening `G ⊂ X` of algebraic spaces, two sections of `𝒪_X` over the same étale
chart which are both killed by the structure map `𝒪_X ⟶ i_*𝒪_G` of the small étale ringed
topoi have product zero: both lie in the defining ideal of `G`, whose square vanishes
(Stacks 05ZK, part (2)). -/
theorem fSharp_mul_eq_zero_of_isFirstOrderThickening (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a b : (smallEtaleRingedTopos B S hS X).O.obj.obj U)
    (ha : (smallEtaleRingedToposHom B S hS
      (ObjectProperty.homMk G.ι : (hG.isThickening B S hS).subspace ⟶ X)).fSharp.hom.app U a = 0)
    (hb : (smallEtaleRingedToposHom B S hS
      (ObjectProperty.homMk G.ι : (hG.isThickening B S hS).subspace ⟶ X)).fSharp.hom.app U b = 0) :
    a * b = 0 := by
  let Z : ClosedSubspaces B S hS X.1 := ⟨G, (hG.isThickening B S hS).1⟩
  have hmem : ∀ c : (smallEtaleRingedTopos B S hS X).O.obj.obj U,
      (smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk G.ι : (hG.isThickening B S hS).subspace ⟶ X)).fSharp.hom.app U c =
          0 → c ∈ definingIdealAt B S hS X Z U := by
    intro c hc
    exact (mem_definingIdealAt_iff B S hS X Z U c).2
      (by rwa [← forgetCommRingSheaf_map_fSharp B S hS])
  exact mul_eq_zero_of_mem_definingIdealAt B S hS Z hG (hmem a ha) (hmem b hb)

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalSubbundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalRestrictionExcess

/-!
# Stacks 0FV7: restriction of the class of a virtual normal sheaf, with excess

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z' = Z ×_X X'` be the
base change of a closed immersion `i : Z ⟶ X` along `f : X' ⟶ X`, both locally of finite type
over `S`, let `𝒩` be a virtual normal sheaf for `Z ⊂ X` and `𝒩'` one for `Z' ⟶ X'`, of arbitrary
ranks, and let `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free
`𝒪_{Z'}`-modules whose dual square against the conormal sheaves commutes. **Stacks 0FV7** asserts
that then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`

in `A^*(Z' ⟶ X')^∧`. The proof is the source's: the base-change clause of Stacks 0FBK
(`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass`) identifies the left
side with `c(Z' ⟶ X', g^*𝒩)`, and Stacks 0FBL
(`Stacks.Chow.completedVirtualNormalGysinClass_eq_of_isTopChernComposition`) for the short exact
sequence on `Z'` rewrites that as the right side; the commuting square is the factorization
hypothesis of Stacks 0FBL (`Stacks.Chow.dualMap_comp_surjection_eq_baseChange_surjection`).

## Main results

* `Stacks.Chow.completedVirtualNormalGysinRestriction_eq_of_isTopChernComposition` —
  **Stacks 0FV7**.

## References

* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (N : VirtualNormalBundle i)
  (𝒩' : VirtualNormalBundle (pullback.snd i f)) (Eb : (pullback i f).Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eb]
  (inc : 𝒩'.bundle ⟶ (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle)
  (pr : (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle ⟶ Eb)

/-- **Stacks 0FV7.** Let `Z' = Z ×_X X'` be the chosen base change of a closed immersion
`i : Z ⟶ X` along `f : X' ⟶ X`, both locally of finite type over the base, let `𝒩` be a virtual
normal sheaf for `Z ⊂ X` and `𝒩'` one for `Z' ⟶ X'`, of arbitrary ranks, and let
`0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_{Z'}`-modules such
that the square of `hcomm` commutes. Then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`

in `A^*(Z' ⟶ X')^∧`, for the classes of Stacks 0FBK, the top Chern class of Stacks 0FA4 and the
composition on completions (a class for `𝟙 ≫ (Z' ⟶ X')`). -/
@[stacks 0FV7 "res(c(Z → X, N)) = c_top(E) ∘ c(Z' → X', N') in A^*(Z' → X')^∧, for a cartesian \
square of closed immersions (the chosen fibre product Z' = Z ×_X X', where restriction lives), \
virtual normal sheaves N, N' of arbitrary rank, and a short exact sequence 0 → N' → g^*N → E → 0 \
of finite locally free modules whose dual square against the conormal sheaves commutes; c the \
completed classes of Tag 0FBK, c_top(E) of Tag 0FA4, the composite read at Z' → X'; proved as in \
the source, by the base-change clause of Tag 0FBK and then Tag 0FBL"]
theorem completedVirtualNormalGysinRestriction_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ 𝒩'.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w)) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClass C sZ sX i hi N) =
      completedBivariantGroup.copy C (Category.id_comp (pullback.snd i f)) _
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (completedBivariantCompositeOfInvertible C (pullback.fst i f ≫ sZ)
          (pullback.fst i f ≫ sZ) (f ≫ sX) (𝟙 _) (pullback.snd i f) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
          (topChernClassOfInvertible C (pullback.fst i f ≫ sZ) Eb)
          (completedVirtualNormalGysinClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) 𝒩')) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  rw [completedBivariantRestriction_completedVirtualNormalGysinClass C sZ sX i hi f N]
  exact completedVirtualNormalGysinClass_eq_of_isTopChernComposition C (pullback.fst i f ≫ sZ)
    (f ≫ sX) (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
    (baseChangeVirtualNormalBundle i f N) 𝒩' Eb inc pr w hseq
    (dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N 𝒩' inc hcomm)

end Stacks.Chow

end

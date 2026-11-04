module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Subbundle
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.SubbundleCompleted
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess

/-!
# Excess intersection for the class of a virtual normal sheaf

Let `(S, δ)` be as in Situation 02QL, let `i : Z ⟶ X` be a closed immersion of schemes locally of
finite type over `S`, let `h : X' ⟶ X` be locally of finite type, and let

```
Z' --i'--→ X'
|          |
g          h
↓          ↓
Z  --i---→ X
```

be the cartesian square, `Z' = Z ×_X X'`. Let `𝒩` be a virtual normal sheaf for `Z ⊂ X`, `𝒩'` one
for `Z' ⊂ X'`, and let `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free
`𝒪_{Z'}`-modules such that the square

```
g^*𝒩^∨ -----→ (𝒩')^∨
|               |
↓               ↓
g^*𝒞_{Z/X} --→ 𝒞_{Z'/X'}
```

commutes. **Stacks 0FV7** asserts `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`. The proof is
the source's: by Stacks 0FBK, `res(c(Z ⟶ X, 𝒩)) = c(Z' ⟶ X', g^*𝒩)`, and the commuting square
says that the conormal surjection of `g^*𝒩` factors through that of `𝒩'` along the dual of
`𝒩' ⟶ g^*𝒩`, so Stacks 0FBL applies.

## Main results

* `Stacks.Chow.VirtualNormalBundle.dualMap_comp_surjection_eq_baseChangeAlong` — the commuting
  square is the factorization hypothesis of Stacks 0FBL for `g^*𝒩`.
* `Stacks.Chow.VirtualNormalBundle.completedBivariantRestriction_completedClass_eq_comp` —
  **Stacks 0FV7**: `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')` in `A^*(Z' ⟶ X')^∧`, ranks
  arbitrary.
* `Stacks.Chow.VirtualNormalBundle.bivariantRestriction_virtualNormalClass_eq_composite` — the
  same when `𝒩'` and `ℰ` have constant ranks `r'` and `e`, in `A^{r'+e}(Z' ⟶ X')`.

## Implementation notes

The restriction `res` of Stacks 0F9Z produces a class for the chosen fibre product
`pullback.snd i h : Z ×_X X' ⟶ X'`, since the cap operations of a bivariant class land in chosen
fibre products; so the cartesian square of the tag is taken to be that one, with
`Z' = Z ×_X X'`, `i' = pullback.snd i h` and `g = pullback.fst i h`. Every cartesian square with
the same bottom and right arrows is canonically isomorphic to it. The horizontal arrow `i'` is
then a closed immersion, as the tag requires.

## References

* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable (C : ChowSituation.{u}) {Z X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {i : Z ⟶ X} [IsClosedImmersion i]
  (hZ : i ≫ sX = sZ) (h : X' ⟶ X) [LocallyOfFiniteType h] (𝒩 : VirtualNormalBundle i)
  (𝒩' : VirtualNormalBundle (pullback.snd i h))
  (inc : 𝒩'.bundle ⟶ (modulePullback (pullback.fst i h).toLRSHom.toShHom).obj 𝒩.bundle)
  (hcomm : pullbackDualMap (pullback.fst i h) 𝒩.bundle ≫ dualMap inc ≫ 𝒩'.surjection =
    (modulePullback (pullback.fst i h).toLRSHom.toShHom).map 𝒩.surjection ≫
      Stacks.Immersion.immersionConormalSheafMap (pullback.snd i h) i (pullback.fst i h) h
        (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i h).w))

omit [LocallyOfFiniteType h] in
include hcomm in
/-- The commuting square of Stacks 0FV7 makes the conormal surjection of `g^*𝒩` factor through
that of `𝒩'` along the dual of `𝒩' ⟶ g^*𝒩`. -/
theorem dualMap_comp_surjection_eq_baseChangeAlong :
    dualMap inc ≫ 𝒩'.surjection =
      (𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip).surjection :=
  dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i h) (pullback.fst i h) h
    (isPullback_pullbackSnd i h) 𝒩 𝒩' inc hcomm

omit [LocallyOfFiniteType h] in
/-- The virtual normal sheaf `𝒩'`, seen through the factorization of the conormal surjection of
`g^*𝒩`, is `𝒩'` itself. -/
theorem ofFactor_baseChangeAlong_eq :
    (𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip).ofFactor 𝒩'.bundle inc 𝒩'.surjection
      (dualMap_comp_surjection_eq_baseChangeAlong h 𝒩 𝒩' inc hcomm) = 𝒩' := by
  cases 𝒩'
  rfl

section ConstantRank

variable (r' e : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r']
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (r' + e)]
  (E : (pullback i h).Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (pr : (modulePullback (pullback.fst i h).toLRSHom.toShHom).obj 𝒩.bundle ⟶ E)
  (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

include hcomm hseq in
/-- **Stacks 0FV7, constant ranks.** For `𝒩'` of constant rank `r'` and `ℰ` of constant rank `e`
(so that `g^*𝒩` has rank `r' + e`),

  `res(c(Z ⟶ X, 𝒩)) = c_e(ℰ) ∘ c(Z' ⟶ X', 𝒩')`   in   `A^{r'+e}(Z' ⟶ X')`,

with `res` the restriction of Stacks 0F9Z and `∘` the composition of Stacks 0B75. -/
theorem bivariantRestriction_virtualNormalClass_eq_composite :
    bivariantRestrictionOfInvertible C sZ sX i hZ h ((r' + e : ℕ) : ℤ)
        (𝒩.virtualNormalClass C sX sZ hZ (r' + e)) =
      BivariantClass.copy C (gysinSystemOfInvertible C) (pullback.fst i h ≫ sZ) (h ≫ sX)
        (Category.id_comp (pullback.snd i h))
        (comp_comp_structureMorphism_eq (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h))
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) (by push_cast; ring)
        (bivariantCompositeOfInvertible C (pullback.fst i h ≫ sZ) (pullback.fst i h ≫ sZ)
          (h ≫ sX) (𝟙 _) (pullback.snd i h) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) e r'
          (GenuineChern.chernClass C (pullback.fst i h ≫ sZ) E e (Fin.last e))
          (𝒩'.virtualNormalClass C (h ≫ sX) (pullback.fst i h ≫ sZ)
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) r')) := by
  rw [bivariantRestriction_virtualNormalClass]
  have key := virtualNormalClass_eq_composite
    (𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip) 𝒩'.bundle inc 𝒩'.surjection
    (dualMap_comp_surjection_eq_baseChangeAlong h 𝒩 𝒩' inc hcomm) C (h ≫ sX) r' e E pr w hseq
    (pullback.fst i h ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h)
  exact key

end ConstantRank

section Completed

variable (E : (pullback i h).Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (pr : (modulePullback (pullback.fst i h).toLRSHom.toShHom).obj 𝒩.bundle ⟶ E)
  (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

include hcomm hseq in
/-- **Stacks 0FV7.** Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over
the base, `h : X' ⟶ X` locally of finite type, and `Z' = Z ×_X X'` with its closed immersion
`i' : Z' ⟶ X'` and projection `g : Z' ⟶ Z`. Let `𝒩` be a virtual normal sheaf for `Z ⊂ X` and
`𝒩'` one for `Z' ⊂ X'`, and let `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite
locally free `𝒪_{Z'}`-modules such that the square
`g^*𝒩^∨ ⟶ (𝒩')^∨ ⟶ 𝒞_{Z'/X'}` = `g^*𝒩^∨ ⟶ g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` commutes (`hcomm`). Then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`   in   `A^*(Z' ⟶ X')^∧`,

where `c(-, -)` are the classes of Stacks 0FBK, `res` the restriction of Stacks 0F9Z on the
completed groups, `c_top(ℰ) ∈ A^*(Z')^∧` the top Chern class of Stacks 0FA4 and `∘` the
composition of Stacks 0FE0; the composite, a class for `𝟙 Z' ≫ i'`, is read at `i'`. No rank is
assumed constant.

The proof is the source's: Stacks 0FBK gives `res(c(Z ⟶ X, 𝒩)) = c(Z' ⟶ X', g^*𝒩)`, the
commuting square says that the conormal surjection of `g^*𝒩` factors through `σ'` along the dual
of `𝒩' ⟶ g^*𝒩`, and Stacks 0FBL concludes. -/
@[stacks 0FV7 "res(c(Z → X, 𝒩)) = c_top(ℰ) ∘ c(Z' → X', 𝒩') in A^*(Z' → X')^∧ for the cartesian \
square Z' = Z ×_X X' of a closed immersion i along X' → X locally of finite type, virtual normal \
sheaves 𝒩 for Z ⊂ X and 𝒩' for Z' ⊂ X', and a short exact sequence 0 → 𝒩' → g^*𝒩 → ℰ → 0 of \
finite locally free O_{Z'}-modules whose dual square against the conormal sheaves commutes; ranks \
arbitrary, c the completed classes of Tag 0FBK, res on completed groups, c_top(ℰ) of Tag 0FA4, \
∘ the composition of Tag 0FE0"]
theorem completedBivariantRestriction_completedClass_eq_comp :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
    haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i h ≫ sZ)
    completedBivariantRestrictionOfInvertible C sZ sX i hZ h (𝒩.completedClass C sX sZ hZ) =
      completedBivariantGroupCongr C (gysinSystemOfInvertible C) (pullback.fst i h ≫ sZ)
        (h ≫ sX) (Category.id_comp (pullback.snd i h))
        (comp_comp_structureMorphism_eq (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h))
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h)
        (completedBivariantCompositeOfInvertible C (pullback.fst i h ≫ sZ)
          (pullback.fst i h ≫ sZ) (h ≫ sX) (𝟙 _) (pullback.snd i h) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h)
          (topChernClassCompleted C (pullback.fst i h ≫ sZ) E).1
          (𝒩'.completedClass C (h ≫ sX) (pullback.fst i h ≫ sZ)
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h))) := by
  rw [← baseChange_completedClass]
  exact completedClass_eq_topChernClassCompleted_comp (𝒩.baseChangePullback h) 𝒩'.bundle inc
    𝒩'.surjection (dualMap_comp_surjection_eq_baseChangeAlong h 𝒩 𝒩' inc hcomm) E C (h ≫ sX)
    (pullback.fst i h ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) pr w hseq

end Completed

end Stacks.Chow.VirtualNormalBundle

end

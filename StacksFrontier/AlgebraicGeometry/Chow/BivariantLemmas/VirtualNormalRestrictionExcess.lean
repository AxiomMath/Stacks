module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundleClass

/-!
# Stacks 0FV7: restriction of a virtual normal Gysin class to a base change, with excess

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z' = Z ×_X X'` be the
base change of a closed immersion `i : Z ⟶ X` along `f : X' ⟶ X`, both locally of finite type
over `S`, let `𝒩` be a virtual normal sheaf for `Z ⊂ X` and `𝒩'` one for `Z' ⟶ X'`, and let
`0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_{Z'}`-modules whose
dual square against the conormal sheaves commutes. **Stacks 0FV7** asserts that then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`.

The source's proof is two steps, and so is the proof here: the base-change clause of Stacks 0FBK
(`Stacks.Chow.bivariantRestriction_virtualNormalGysinClass`) identifies `res(c(Z ⟶ X, 𝒩))` with
`c(Z' ⟶ X', g^*𝒩)`, and Stacks 0FBL
(`Stacks.Chow.virtualNormalBundleClass_cap_eq_chernCap_comp`), applied to the short exact sequence
on `Z'`, rewrites that as `c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`. The commuting square is the factorization
hypothesis of Stacks 0FBL for `g^*𝒩`
(`Stacks.Chow.dualMap_comp_surjection_eq_baseChange_surjection`).

## Main results

* `Stacks.Chow.virtualNormalBundleClassRestrictionCap_eq_chernCap_comp` — Stacks 0FV7 at constant
  rank, on cap operations.
* `Stacks.Chow.virtualNormalBundleClassRestriction_eq_of_isTopChernComposition` — Stacks 0FV7 at
  constant rank, `res(c(Z ⟶ X, 𝒩)) = c_e(ℰ) ∘ c(Z' ⟶ X', 𝒩')` in `A^{m' + e}(Z' ⟶ X')`.

## Implementation notes

The square is the *chosen* fibre product `Z ×_X X'`, where the restriction of Stacks 0F9Z
(`Stacks.Chow.bivariantRestriction`) lands; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess`. The classes
are the classes `Stacks.Chow.virtualNormalBundleClass` of Stacks 0FBK, at the Gysin system of the
first Chern class rule.

The results here are for constant ranks: `𝒩` of rank `m' + e`, `𝒩'` of rank `m'` and `ℰ` of rank
`e`, so the equality holds in `A^{m' + e}(Z' ⟶ X')`. The source states Stacks 0FV7 for arbitrary
ranks, in `A^*(Z' ⟶ X')^∧`; that form is not proved here, and these results are not registered
under the tag.

## References

* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### Stacks 0FV7 at constant rank -/

section Main

variable (C : ChowSituation.{u}) {Z X X' : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (f : X' ⟶ X) [LocallyOfFiniteType f]
  (m' e : ℕ) (N : VirtualNormalBundle i)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle (m' + e)]
  (𝒩' : VirtualNormalBundle (pullback.snd i f))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle m']
  (Eb : (pullback i f).Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (inc : 𝒩'.bundle ⟶
    (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle)
  (pr : (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle ⟶ Eb)

/-- **Stacks 0FV7 at constant rank, on cap operations.** Let `Z' = Z ×_X X'` be the chosen base
change of a closed immersion `i : Z ⟶ X` along `f : X' ⟶ X`, both locally of finite type over
the base, let `𝒩` be a virtual normal sheaf for `Z ⊂ X` of constant rank `m' + e`, let `𝒩'` be one
for `Z' ⟶ X'` of constant rank `m'`, and let `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of
finite locally free `𝒪_{Z'}`-modules with `ℰ` of constant rank `e`, such that the square of
`hcomm` commutes. Then

  `res(c(Z ⟶ X, 𝒩)) ∩ α = c_e(ℰ) ∩ (c(Z' ⟶ X', 𝒩') ∩ α)`

on every test scheme `g₀ : T ⟶ X'`, in every degree and for every `α ∈ A_k(T)`.

The proof is the source's. By the base-change clause of Stacks 0FBK
(`Stacks.Chow.bivariantRestriction_virtualNormalGysinClass`), `res(c(Z ⟶ X, 𝒩))` is
`c(Z' ⟶ X', g^*𝒩)`. The commuting square makes the conormal surjection of the virtual normal sheaf
`g^*𝒩` of Stacks 0FBJ factor through that of `𝒩'`, and Stacks 0FBL in the form
`Stacks.Chow.virtualNormalBundleClass_cap_eq_chernCap_comp` concludes. -/
theorem virtualNormalBundleClassRestrictionCap_eq_chernCap_comp
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ 𝒩'.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w))
    {T : Scheme.{u}} (g₀ : T ⟶ X') [LocallyOfFiniteType g₀] (k : ℤ)
    (α : chowGroup C (g₀ ≫ (f ≫ sX)) k) :
    (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f ((m' + e : ℕ) : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (virtualNormalBundleClass C sZ sX i hi N (m' + e))).cap g₀ k α =
      chowGroupDegreeEquiv C (pullback.fst (pullback.snd i f) g₀ ≫ (pullback.fst i f ≫ sZ))
        (by push_cast; ring)
        (subbundleChernClassCap C (pullback.fst i f ≫ sZ) (pullback.snd i f) m' e Eb g₀ k
          ((virtualNormalBundleClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) 𝒩' m').cap g₀ k α)) := by
  rw [bivariantRestriction_virtualNormalGysinClass C sZ sX i hi f N (m' + e)]
  exact virtualNormalBundleClass_cap_eq_chernCap_comp C (pullback.fst i f ≫ sZ) (f ≫ sX)
    (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
    (baseChangeVirtualNormalBundle i f N) 𝒩' m' e Eb inc pr (gysinSystemOfInvertible C) w hseq
    (dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N 𝒩' inc hcomm)
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ _ _ _ _ (m' + e))
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ _ _ _ _ m') g₀ k α

/-- **Stacks 0FV7 at constant rank**, as an equality in `A^{m' + e}(Z' ⟶ X')`: in the situation
of `Stacks.Chow.virtualNormalBundleClassRestrictionCap_eq_chernCap_comp`,

  `res(c(Z ⟶ X, 𝒩)) = c_e(ℰ) ∘ c(Z' ⟶ X', 𝒩')`,

with `c_e(ℰ) = c_top(ℰ) ∈ A^e(Z')` the Chern class of Stacks 0B7H and the composite of Stacks
0B75, a class for `𝟙 ≫ (Z' ⟶ X')` of degree `e + m'`. By the base-change clause of Stacks 0FBK
the left side is `c(Z' ⟶ X', g^*𝒩)`, and this is Stacks 0FBL
(`Stacks.Chow.virtualNormalBundleClass_eq_of_isTopChernComposition`) for `g^*𝒩`. -/
theorem virtualNormalBundleClassRestriction_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ 𝒩'.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w)) :
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f ((m' + e : ℕ) : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (virtualNormalBundleClass C sZ sX i hi N (m' + e)) =
      BivariantClass.copy C (gysinSystemOfInvertible C) (pullback.fst i f ≫ sZ) (f ≫ sX)
        (Category.id_comp (pullback.snd i f))
        (comp_comp_structureMorphism_eq (Category.id_comp (pullback.fst i f ≫ sZ))
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f))
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (by push_cast; ring)
        (bivariantCompositeOfInvertible C (pullback.fst i f ≫ sZ) (pullback.fst i f ≫ sZ)
          (f ≫ sX) (𝟙 _) (pullback.snd i f) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (e : ℤ) (m' : ℤ)
          (GenuineChern.chernClass C (pullback.fst i f ≫ sZ) Eb e (Fin.last e))
          (virtualNormalBundleClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) 𝒩' m')) := by
  rw [bivariantRestriction_virtualNormalGysinClass C sZ sX i hi f N (m' + e)]
  exact virtualNormalBundleClass_eq_of_isTopChernComposition C (pullback.fst i f ≫ sZ) (f ≫ sX)
    (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
    (baseChangeVirtualNormalBundle i f N) 𝒩' m' e Eb inc pr w hseq
    (dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N 𝒩' inc hcomm)

end Main

end Stacks.Chow

end

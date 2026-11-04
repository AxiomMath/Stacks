module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality

/-!
# The inverse image of the inverse of an invertible module

Let `q : W ⟶ V` be a morphism of algebraic spaces over a scheme `S` and let `L` be an invertible
`𝒪_V`-module. The inverse image of `L^{⊗ -1}` along `q` is the inverse `(q^*L)^{⊗ -1}` of the
inverse image of `L`. On Picard classes this is the additivity of the pullback
`Pic(V) ⟶ Pic(W)`, which is a homomorphism of groups and therefore commutes with negation; two
invertible modules are isomorphic exactly when their classes agree.

## Main results

* `AlgebraicGeometry.Space.nonempty_modulePullback_tensorPower_neg_one_iso`:
  `q^*(L^{⊗ -1}) ≅ (q^*L)^{⊗ -1}`.
* `AlgebraicGeometry.Space.nonempty_modulePullback_tensorPower_neg_one_iso_structureModule`: if
  `q^*L` is trivial, so is `q^*(L^{⊗ -1})`.
* `AlgebraicGeometry.Space.nontrivial_sections_of_ne_zero`: a nonzero map `𝒪 ⟶ M` is a nonzero
  global section of `M`.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorPower (tensorPower)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The inverse image of `L^{⊗ -1}` is the inverse of the inverse image of `L`.** For a
morphism `q : W ⟶ V` of algebraic spaces and an invertible `𝒪_V`-module `L`,
`q^*(L^{⊗ -1}) ≅ (q^*L)^{⊗ -1}`: the pullback of Picard classes is a homomorphism of groups. -/
theorem nonempty_modulePullback_tensorPower_neg_one_iso {V W : AlgebraicSpaces B S hS}
    (q : W ⟶ V) (L : Modules.{u, u} B S hS V.1 V.2) [hL : IsInvertibleModule V L] :
    haveI : IsInvertibleModule W ((modulePullback B S hS q).obj L) :=
      modulePullbackInvertible q L hL
    haveI := isEquivalence_tensorRightFunctor B S hS V.1 V.2 L
    haveI := isEquivalence_tensorRightFunctor B S hS W.1 W.2 ((modulePullback B S hS q).obj L)
    Nonempty ((modulePullback B S hS q).obj
        (tensorPower (structureSheaf B S hS V.1 V.2).obj
          (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (-1)) ≅
      tensorPower (structureSheaf B S hS W.1 W.2).obj
        (structureRingPresheaf_isSheaf B S hS W.1 W.2) ((modulePullback B S hS q).obj L) (-1)) := by
  have hqL : IsInvertibleModule W ((modulePullback B S hS q).obj L) :=
    modulePullbackInvertible q L hL
  have := isEquivalence_tensorRightFunctor B S hS V.1 V.2 L
  have := isEquivalence_tensorRightFunctor B S hS W.1 W.2 ((modulePullback B S hS q).obj L)
  have hinv := Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
    (structureSheaf B S hS V.1 V.2).obj (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (-1)
  have hinv' := Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
    (structureSheaf B S hS W.1 W.2).obj (structureRingPresheaf_isSheaf B S hS W.1 W.2)
    ((modulePullback B S hS q).obj L) (-1)
  refine (picardClass_eq_picardClass_iff W _ _ (modulePullbackInvertible q _ hinv) hinv').1 ?_
  rw [← picardPullback_picardClass q _ hinv]
  have h1 : picardClass V _ hinv = -picardClass V L hL :=
    Stacks.SheafOfModules.picardClass_tensorPower_neg_one (structureSheaf B S hS V.1 V.2).obj
      (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (hL := hL)
  have h2 : picardClass W _ hinv' = -picardClass W _ hqL :=
    Stacks.SheafOfModules.picardClass_tensorPower_neg_one (structureSheaf B S hS W.1 W.2).obj
      (structureRingPresheaf_isSheaf B S hS W.1 W.2) ((modulePullback B S hS q).obj L) (hL := hqL)
  rw [h1, h2, ← picardPullbackHom_apply, map_neg, picardPullbackHom_apply,
    picardPullback_picardClass]

/-- **If the inverse image of an invertible module is trivial, so is the inverse image of its
inverse.** -/
theorem nonempty_modulePullback_tensorPower_neg_one_iso_structureModule
    {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (L : Modules.{u, u} B S hS V.1 V.2)
    [hL : IsInvertibleModule V L]
    (h : Nonempty ((modulePullback B S hS q).obj L ≅ structureModule W)) :
    haveI := isEquivalence_tensorRightFunctor B S hS V.1 V.2 L
    Nonempty ((modulePullback B S hS q).obj
        (tensorPower (structureSheaf B S hS V.1 V.2).obj
          (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (-1)) ≅ structureModule W) := by
  have := isEquivalence_tensorRightFunctor B S hS V.1 V.2 L
  have hinv := Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
    (structureSheaf B S hS V.1 V.2).obj (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (-1)
  refine (picardClass_eq_zero_iff W _ (modulePullbackInvertible q _ hinv)).1 ?_
  rw [← picardPullback_picardClass q _ hinv]
  have h1 : picardClass V _ hinv = -picardClass V L hL :=
    Stacks.SheafOfModules.picardClass_tensorPower_neg_one (structureSheaf B S hS V.1 V.2).obj
      (structureRingPresheaf_isSheaf B S hS V.1 V.2) L (hL := hL)
  rw [h1, ← picardPullbackHom_apply, map_neg, picardPullbackHom_apply,
    picardPullback_picardClass, (picardClass_eq_zero_iff W _ _).2 h, neg_zero]

/-- **A nonzero map out of the structure sheaf is a nonzero global section.** -/
theorem nontrivial_sections_of_ne_zero {Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Z.1 Z.2} (s : structureModule Z ⟶ M) (hs : s ≠ 0) :
    Nontrivial M.sections :=
  ⟨⟨M.unitHomEquiv s, M.unitHomEquiv 0, fun h => hs (M.unitHomEquiv.injective h)⟩⟩

end AlgebraicGeometry.Space

end

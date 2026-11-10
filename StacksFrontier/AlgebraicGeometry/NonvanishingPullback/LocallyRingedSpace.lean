module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0H78 for a morphism of locally ringed spaces

Stacks Tag 0H78 is Remark 17.25.11: for a morphism of locally ringed spaces `f : Y ⟶ X`, an
`𝒪_X`-module `L` and a global section `s`, the inverse image `f^{-1}(X_s)` of the nonvanishing
locus is the nonvanishing locus `Y_{f^* s}` of the pulled-back section. That is the generality the
remark is stated in, and it is the generality here; the scheme case is the sibling result
`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`, which is what the ampleness theory
consumes.

Nothing about `f` is assumed beyond its being a morphism of locally ringed spaces, and nothing
about `L` at all: no invertibility, no quasi-coherence, no finiteness. Locality of `f` is used
exactly once, to know that its maps on stalks are local homomorphisms.

## Main definitions

* `Stacks.NonvanishingPullback.pullbackSections`: `f^* s` as a restriction-compatible family,
  which is the form the ringed-space statement of Stacks Tag 01CY takes its argument in. It is
  the pullback of the global section, spread back out over the opens by
  `Stacks.SectionRingGeometric.sectionsEquivObj`.

## Main results

* `Stacks.NonvanishingPullback.preimage_nonvanishingLocus_lrs`: **Stacks Tag 0H78.**

## Implementation notes

**The family is produced by the terminal-object equivalence, not by `sectionsMk`.** A
restriction-compatible family out of one global section is exactly what
`Stacks.SectionRingGeometric.sectionsEquivObj` inverts, and using it avoids writing the
compatibility proof a second time — the inverse image of `⊤` being `⊤` on the nose is what makes
the global section of the pullback available in the first place.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open scoped Stacks.NonvanishingTrivialize

universe u

namespace Stacks.NonvanishingPullback

/-- **`𝔪_x · M_x` means the same thing in the two spellings**, at the ringed-space statement of
Stacks Tag 01CY. The ringed-space analogue of
`Stacks.NonvanishingPullback.mem_maximalSmul_iff`. -/
theorem mem_maximalSmul_iff_lrs {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheaf Z.sheaf))
    [∀ x : Z, IsLocalRing (Z.presheaf.stalk x)] (y : Z.carrier)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y) :
    m ∈ Stacks.NonvanishingTrivialize.maximalSmul Z M y ↔
      letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Z M.val y
      m ∈ IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z y) •
        (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z y)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Z M.val y)) := by
  change m ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk y) •
    (⊤ : Submodule (Z.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y)) ↔ _
  rw [← stalkModule_eq M y]
  exact Iff.rfl

variable {Y X : LocallyRingedSpace.{u}} (f : Y ⟶ X)
  (L : SheafOfModules.{u} (structureSheaf X.toRingedSpace.sheaf))

/-- **The pullback of a global section as a restriction-compatible family.** Its value over `⊤` is
the image of `s`'s value over `⊤` under the unit of the module-pullback adjunction. -/
def pullbackSections (s : L.sections) : ((modulePullback f.toShHom).obj L).sections :=
  (Stacks.SectionRingGeometric.sectionsEquivObj CategoryTheory.Limits.isTerminalTop
    ((modulePullback f.toShHom).obj L).val).symm
      (Stacks.RingedSpace.pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤)))

/-- The value of `pullbackSections f L s` over `⊤` is the image of the value of `s` over `⊤`
under the unit of the module-pullback adjunction. -/
@[simp] theorem pullbackSections_eval_top (s : L.sections) :
    (pullbackSections f L s).eval (op ⊤) =
      Stacks.RingedSpace.pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤)) :=
  (Stacks.SectionRingGeometric.sectionsEquivObj CategoryTheory.Limits.isTerminalTop
    ((modulePullback f.toShHom).obj L).val).apply_symm_apply _

/-- **Stacks Tag 0H78.** For a morphism of locally ringed spaces, the inverse image of the
nonvanishing locus of a global section of a module is the nonvanishing locus of the pulled-back
section. -/
@[stacks 0H78, ega "II 4.6.13.1" "more general"]
theorem preimage_nonvanishingLocus_lrs (s : L.sections) :
    f.base ⁻¹' Stacks.NonvanishingTrivialize.nonvanishingLocus X.toRingedSpace L s =
      Stacks.NonvanishingTrivialize.nonvanishingLocus Y.toRingedSpace
        ((modulePullback f.toShHom).obj L) (pullbackSections f L s) := by
  refine Set.ext fun y => not_congr ?_
  refine Iff.trans (mem_maximalSmul_iff_lrs L (f.base y) _) ?_
  refine Iff.trans ?_
    (mem_maximalSmul_iff_lrs ((modulePullback f.toShHom).obj L) y _).symm
  refine Iff.trans
    (mem_maximalIdeal_smul_iff_one_tmul
      (instAlg := Stacks.PullbackTensorIso.commStalkAlgebra f.toShHom y)
      (instLoc := isLocalHom_commStalkRingMap_lrs f y)
      (instMod := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val
        (f.base y))
      ((TopCat.Presheaf.Γgerm L.val.presheaf (f.base y)).hom (s.eval (op ⊤)))) ?_
  refine Iff.trans
    (mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.PullbackTensorIso.pullbackStalkEquiv f.toShHom y L) _) ?_
  refine Iff.of_eq (congrArg (fun z => z ∈
    IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace
      y) • ⊤) ?_)
  refine Eq.trans (Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul f.toShHom y L ⊤ trivial
    (s.eval (op ⊤))) ?_
  exact congrArg _ (pullbackSections_eval_top f L s).symm

end Stacks.NonvanishingPullback

end

module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Algebra
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.AmpleLocallyClosed.Basic

/-!
# Stacks Tag 0H78: the inverse image of a nonvanishing locus

For a morphism of schemes `i : X' ⟶ X`, an `𝒪_X`-module `M` and a global section `s` of `M`, the
inverse image of the nonvanishing locus `X_s` is the nonvanishing locus `X'_{i^* s}` of the
pulled-back section.

`StacksFrontier/AlgebraicGeometry/AmpleLocallyClosed/Basic.lean` carries this statement as the
unproved premise `Stacks.AmpleLocallyClosed.SectionPullbackCompatible`, and gives as its reason
that "the comparison of `Stacks.ModuleStalk.maximalSmul` across that identification is not
proved". **That is what is proved here**, and it needs no invertibility, no quasi-coherence and no
hypothesis on `i` whatsoever: the statement is about one arbitrary module and one arbitrary
morphism of schemes.

## Main definitions

* `Stacks.NonvanishingPullback.pullbackGlobalSection`: `i^* s`, the image of a global section
  under the unit of the module-pullback adjunction. No restriction map is interposed: the inverse
  image of `⊤` is `⊤` on the nose.

## Main results

* `Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff`: the pointwise form.
* `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`: **Stacks Tag 0H78.**

## The route

Three inputs, each already in the repository or in the two sibling files:

* **Stacks Tag 0098**, `Stacks.PullbackTensorIso.pullbackStalkEquiv`: the stalk of `i^* M` at `x'`
  is `𝒪_{X',x'} ⊗_{𝒪_{X,i x'}} M_{i x'}`, and
  `Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul` says that identification carries
  `1 ⊗ germ s` to the germ of `i^* s`.
* **the algebra**, `Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul`: base change
  along a local homomorphism detects `𝔪 · M`.
* **the two bridges** of `StacksFrontier/AlgebraicGeometry/NonvanishingPullback/StalkBridge.lean`:
  the module structure Tag 0098 is stated over is the one ampleness is stated over, and the ring
  homomorphism Tag 0098 is taken along is the stalk map of `i`, hence local.

## Implementation notes

**The instance arguments of the algebraic lemma are passed by name.** The stalk of `M` carries two
equal but distinct `𝒪_{X,i x'}`-module structures, and the tensor product in the statement of
Stacks Tag 0098 is formed over the one from Stacks Tag 01CB; instance search would supply the
other, and the two tensor products would then not be the same type. So
`Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul` is applied with
`(instMod := …)` and `(instAlg := …)` rather than by counting `@` positions.

**The algebra structure on the stalks is the one `Stacks.PullbackTensorIso.pullbackStalkEquiv` is
stated over**, `Stacks.PullbackTensorIso.commStalkAlgebra`, which is a `local instance` in its own
file and therefore has to be named here. `Stacks.PullbackTensorIso.commStalkModule` is *not*
interchangeable with it: `RingHom.toModule` and the `Module` derived from `RingHom.toAlgebra` are
different terms, and only the latter is what the equivalence's tensor product uses.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingPullback

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (M : X.Modules)

/-- **The pullback of a global section** along a morphism of schemes: the image of `s` under the
unit of the module-pullback adjunction, over the inverse image of `⊤`, which is `⊤` itself. -/
def pullbackGlobalSection (s : Γ(M, ⊤)) :
    Γ((modulePullback i.toLRSHom.toShHom).obj M, ⊤) :=
  Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom M (op ⊤) s

/-- **Stacks Tag 0H78, pointwise**: a point of `X'` lies in the nonvanishing locus of `i^* s`
exactly when its image lies in the nonvanishing locus of `s`. -/
theorem mem_nonvanishingLocus_pullback_iff (s : Γ(M, ⊤)) (x' : X') :
    x' ∈ Stacks.Ample.nonvanishingLocus ((modulePullback i.toLRSHom.toShHom).obj M)
        (pullbackGlobalSection i M s) ↔
      i.base x' ∈ Stacks.Ample.nonvanishingLocus M s := by
  refine (not_congr ?_).symm
  refine Iff.trans (mem_maximalSmul_iff M (i.base x') _) ?_
  refine Iff.trans ?_ (mem_maximalSmul_iff ((modulePullback i.toLRSHom.toShHom).obj M) x' _).symm
  refine Iff.trans
    (mem_maximalIdeal_smul_iff_one_tmul
      (instAlg := Stacks.PullbackTensorIso.commStalkAlgebra i.toLRSHom.toShHom x')
      (instLoc := isLocalHom_commStalkRingMap i x')
      (instMod := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val
        (i.base x'))
      ((M.presheaf.Γgerm (i.base x')).hom s)) ?_
  refine Iff.trans
    (mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.PullbackTensorIso.pullbackStalkEquiv i.toLRSHom.toShHom x' M) _) ?_
  exact Iff.of_eq (congrArg (fun z => z ∈
    IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      X'.toRingedSpace x') • ⊤)
    (Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul i.toLRSHom.toShHom x' M ⊤ trivial s))

/-- **Stacks Tag 0H78.** The inverse image of the nonvanishing locus of `s` is the nonvanishing
locus of `i^* s`. -/
theorem preimage_nonvanishingLocus (s : Γ(M, ⊤)) :
    i.base ⁻¹' Stacks.Ample.nonvanishingLocus M s =
      Stacks.Ample.nonvanishingLocus ((modulePullback i.toLRSHom.toShHom).obj M)
        (pullbackGlobalSection i M s) :=
  Set.ext fun x' => (mem_nonvanishingLocus_pullback_iff i M s x').symm

end Stacks.NonvanishingPullback

end

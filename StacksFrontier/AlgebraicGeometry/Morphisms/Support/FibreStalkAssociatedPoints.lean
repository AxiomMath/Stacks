module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassin.TensorPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkModule
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Associated points of a module restricted to a scheme-theoretic fibre

Let `f : X ⟶ S` be a morphism of schemes, `F` an `𝒪_X`-module and `x` a point of `X`. The
restriction of `F` to the scheme-theoretic fibre through `x` has, at the point `f.asFiber x` of
that fibre, the stalk `F_x/𝔪_{f x}F_x`, and the local ring there is `𝒪_{X,x}/𝔪_{f x}𝒪_{X,x}`.
This file turns the geometric condition "`f.asFiber x` is an associated point of the restriction"
into the commutative algebra condition "the maximal ideal of `𝒪_{X,x}` is an associated prime of
the reduction `F_x/𝔪_{f x}F_x`", which is the form in which a statement about the relative
assassin becomes a statement about one stalk and one ideal.

Both sides are the strict condition of Stacks 00LA — the maximal ideal is *literally* the
annihilator of an element — and no Noetherian hypothesis is needed: the two sides are matched by
a surjection of local rings and an additive equivalence semilinear over it, which is exactly the
situation of `Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_congr`. The surjection
is the stalk map of the fibre inclusion, whose kernel is the fibre ideal
(`AlgebraicGeometry.Scheme.Hom.ker_stalkMap_fiberι`), and the equivalence comes from the stalk
formula for a pullback of modules (Stacks 0098) composed with the identification of
`(A/I) ⊗_A M` with `M/IM`, which is `AlgebraicGeometry.quotientBaseChangeStalkEquiv`.

## Main results

* `AlgebraicGeometry.isAssociatedPoint_asFiber_iff`: the point `f.asFiber x` of the fibre is
  associated to the restriction of `F` to the fibre exactly when the maximal ideal of `𝒪_{X,x}`
  is an associated prime of `F_x/𝔪_{f x}F_x`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The associated points of a module on a fibre, read on the source stalk.** The point
`f.asFiber x` of the scheme-theoretic fibre of `f : X ⟶ S` through `x` is an associated point of
the restriction of `F` to that fibre exactly when the maximal ideal of `𝒪_{X,x}` is an associated
prime of the reduction `F_x/𝔪_{f x}F_x`.

The stalk map of the fibre inclusion is a surjection of local rings with kernel the fibre ideal,
and the stalk of the pullback of `F` is `𝒪_{X_{f x}, f.asFiber x} ⊗_{𝒪_{X,x}} F_x`, hence is that
reduction; the strict associated-prime condition at the maximal ideal transfers across such a
pair. -/
theorem isAssociatedPoint_asFiber_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) :
    f.asFiber x ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.fiberι (f x) (f.asFiber x)) ⧸
          (f.stalkFibreIdeal (f.fiberι (f x) (f.asFiber x)) •
            (⊤ : Submodule (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
                (f.fiberι (f x) (f.asFiber x))))))
        (maximalIdeal (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))) := by
  classical
  let : Algebra (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.toAlgebra
  let : Module (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    Module.compHom _ ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
  let : IsScalarTower (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hsurj : Function.Surjective ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom :=
    (f.fiberι (f x)).stalkMap_surjective (f.asFiber x)
  have hlocal : IsLocalHom ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom :=
    (f.fiberι (f x)).toLRSHom.prop (f.asFiber x)
  have eL : TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)
      ≃ₗ[(f.fiber (f x)).presheaf.stalk (f.asFiber x)]
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ⊗[X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))]
        TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
          (f.fiberι (f x) (f.asFiber x)) :=
    Classical.choose (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      (f.fiberι (f x)).toLRSHom.toShHom F (f.asFiber x))
  have heR := Classical.choose_spec (quotientStalk_bridge f x)
  have eAlg : (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)) ⧸
        f.stalkFibreIdeal (f.fiberι (f x) (f.asFiber x)))
      ≃ₐ[X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))]
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    AlgEquiv.ofRingEquiv (f := Classical.choose (quotientStalk_bridge f x)) fun a => heR a
  refine (Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_congr
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
    (quotientBaseChangeStalkEquiv _ eAlg eL).symm.toAddEquiv (fun r m => ?_) hsurj).symm
  exact map_smul (quotientBaseChangeStalkEquiv _ eAlg eL).symm r m

end AlgebraicGeometry

end

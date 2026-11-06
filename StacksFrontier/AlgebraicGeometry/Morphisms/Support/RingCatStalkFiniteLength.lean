module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk

/-!
# The stalk of a coherent module supported at a point, over the `RingCat`-valued stalk ring

Let `X` be a locally Noetherian scheme and `F` a coherent `𝒪_X`-module whose support is
contained in `{x}`. The stalk of `F` at `x` then has finite length, and this file records that
over the `RingCat`-valued stalk of the sheaf of rings, over which the stalk functor
`AlgebraicGeometry.modulesRingCatStalkFunctor x` takes its values, rather than over the local ring
`𝒪_{X,x}`. The two stalk rings are matched by `AlgebraicGeometry.ringCatStalkRingEquiv`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkObjStalkRing`: the stalk of a sheaf of `𝒪_X`-modules,
  with its target type written over `Stacks.Cohomology.DerivedInternalHomStalk.stalkRing`.

## Main results

* `isFiniteLength_of_ringEquiv_smul_eq`: finite length passes between two module structures on
  one abelian group whose scalar actions are matched by a ring isomorphism.
* `Stacks.Chow.isFiniteLength_ringCatStalk_of_supp_subset_singleton`: the stalk at `x` of a
  coherent module supported in `{x}` has finite length over the `RingCat`-valued stalk ring.
* `Stacks.Chow.isFiniteLength_stalkRing_of_supp_subset_singleton`: the same over the
  `Stacks.Cohomology.DerivedInternalHomStalk.stalkRing` spelling of that ring.

## References

* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- **Finite length passes along a ring isomorphism that matches two scalar actions.** If an
abelian group `M` is a module over two rings `R` and `S`, and a ring isomorphism `e : S ≃+* R`
carries the `S`-action to the `R`-action, then `M` has finite length over `S` as soon as it has
finite length over `R`. -/
theorem isFiniteLength_of_ringEquiv_smul_eq {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M]
    [Module R M] [Module S M] (e : S ≃+* R) (he : ∀ (s : S) (m : M), e s • m = s • m)
    (h : IsFiniteLength R M) : IsFiniteLength S M := by
  have : RingHomInvPair (e.symm : R →+* S) (e : S →+* R) := RingHomInvPair.of_ringEquiv_symm e
  have : RingHomInvPair (e : S →+* R) (e.symm : R →+* S) := RingHomInvPair.of_ringEquiv e
  let f : M ≃ₛₗ[(e.symm : R →+* S)] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by simpa using he (e.symm r) m
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  obtain ⟨_, hA⟩ := h
  exact ⟨isNoetherian_of_linearEquiv f,
    (Submodule.orderIsoMapComap f).symm.toOrderEmbedding.wellFounded hA⟩

namespace Stacks.Chow

/-- **The stalk at `x` of a coherent module supported in `{x}` has finite length over the
`RingCat`-valued stalk of the sheaf of rings**, the ring over which
`AlgebraicGeometry.modulesRingCatStalkFunctor x` takes its values. -/
theorem isFiniteLength_ringCatStalk_of_supp_subset_singleton {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) (F : X.Modules) [F.IsCoherent]
    (hsupp : (_root_.SheafOfModules.supp F : Set X) ⊆ {x}) :
    IsFiniteLength
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x))
      ((AlgebraicGeometry.modulesRingCatStalkFunctor x).obj F) := by
  let : Module (ToType (X.presheaf.stalk x))
      ((AlgebraicGeometry.modulesRingCatStalkFunctor x).obj F).carrier :=
    inferInstanceAs (Module (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)))
  exact isFiniteLength_of_ringEquiv_smul_eq (AlgebraicGeometry.ringCatStalkRingEquiv x)
    (SemilinearStalk.comm_smul_eq X.presheaf x F.val)
    (isFiniteLength_stalk_of_supp_subset_singleton F x hsupp)

/-! ### The statement at the `stalkRing` spelling of the stalk ring -/

section StalkRing

attribute [local instance] Stacks.Cohomology.DerivedInternalHomStalk.stalkCommRing

/-- The stalk at `x` of a sheaf of `𝒪_X`-modules, with its target type written as `ModuleCat`
over `Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x`; as a module it is
`AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing X.toRingedSpace) x F`. -/
abbrev _root_.AlgebraicGeometry.SheafOfModules.stalkObjStalkRing
    {X : Scheme.{u}} (x : X) (F : X.Modules) :
    ModuleCat.{u} (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x) :=
  AlgebraicGeometry.SheafOfModules.stalkObj (_root_.structureSheafRing X.toRingedSpace) x F

/-- **The stalk at `x` of a coherent module supported in `{x}` has finite length over
`Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x`.** -/
theorem isFiniteLength_stalkRing_of_supp_subset_singleton {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) (F : X.Modules) [F.IsCoherent]
    (hsupp : (_root_.SheafOfModules.supp F : Set X) ⊆ {x}) :
    IsFiniteLength
      (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x)
      (AlgebraicGeometry.SheafOfModules.stalkObjStalkRing x F) :=
  isFiniteLength_ringCatStalk_of_supp_subset_singleton x F hsupp

end StalkRing

end Stacks.Chow

end

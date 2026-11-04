module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteEtaleSections

/-!
# The canonical Frobenius trace on a scheme finite over the base field

For a scheme `Y` finite over the finite field `k`, as in Step 2 of the proof of
[Stacks, Tag 03UG], the trace of the canonical endomorphism `π_Y^*` of `RΓ(Y_k̄, C|_{Y_k̄})` is the
trace of an endomorphism of a complex of modules of global sections, with no derived functor left.
It rests on two exactness statements.

* Global sections over the spectrum of a separably closed field `Ω` are exact: they are the stalk
  at the identity geometric point, the identity being an initial étale neighbourhood of itself,
  and a stalk functor is exact.
* For `Y` finite over `k` the structure morphism `Y_k̄ ⟶ Spec k̄` is finite, so its direct image
  is exact.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleGlobalSectionsIsoSheafFiber` — global sections over
  `Spec Ω` are the stalk at the identity geometric point.

## Main results

* `Stacks.EtaleCohomology.etaleModuleGlobalSections_preservesFiniteColimits` — global sections
  over `Spec Ω` are right exact, hence exact.
* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_isFinite`
  — for `Y` finite over `k`, the trace of `π_Y^*` on `RΓ(Y_k̄, C|_{Y_k̄})` is the trace of the
  termwise endomorphism of `Γ(Spec k̄, pr_* (C|_{Y_k̄}))`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Global sections over the spectrum of a separably closed field -/

section SepClosed

variable (Λ : Type r) [Ring Λ] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **Global sections over the spectrum of a separably closed field are the stalk at the identity
geometric point.**  Both are evaluation at the final object of the small étale site, the stalk
because the identity is an initial étale neighbourhood of itself. -/
def etaleModuleGlobalSectionsIsoSheafFiber :
    etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)) ≅
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) :=
  Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleMkId (Spec (.of Ω))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (presheafFiberSelfIso (𝟙 (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ))

/-- Global sections over the spectrum of a separably closed field preserve finite colimits, being
a stalk functor. -/
instance etaleModuleGlobalSections_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))) :=
  preservesFiniteColimits_of_natIso (etaleModuleGlobalSectionsIsoSheafFiber Λ Ω).symm

/-- Global sections preserve finite limits, being a right adjoint. -/
instance etaleModuleGlobalSections_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (etaleModuleGlobalSections.{u, r} Λ X) :=
  inferInstance

end SepClosed

/-! ### The trace for a scheme finite over the base field -/

section Finite

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- For `Y` finite over `k` the direct image along `Y_k̄ ⟶ Spec k̄` preserves finite limits. -/
instance preservesFiniteLimits_directImage_snd :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar))) :=
  inferInstance

/-- For `Y` finite over `k` the direct image along `Y_k̄ ⟶ Spec k̄` preserves finite colimits,
being exact. -/
instance preservesFiniteColimits_directImage_snd [IsFinite Y.hom] :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar))) :=
  ((exactFunctor_iff _).1
    (etaleModuleDirectImage_exact_of_isIntegralHom Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar)))).2

/-- The twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` given by the Frobenius base change twist, as a
morphism of bounded below complexes. -/
abbrev frobeniusRestrictionTwist (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C ⟶
      (etaleModuleDirectImage.{u, r} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          C) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app C.obj)

/-- The complex `Γ(Spec k̄, pr_* (C|_{Y_k̄}))` of global sections, termwise. -/
abbrev frobeniusRestrictionSectionsComplex
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar))).mapCochainComplexPlus.obj
    ((etaleModuleDirectImage.{u, r} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C))

/-- The termwise endomorphism of `Γ(Spec k̄, pr_* (C|_{Y_k̄}))` induced by the Frobenius base
change twist and the identification `pr_* π̄_* = pr_*`. -/
abbrev frobeniusRestrictionSectionsEndo
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    frobeniusRestrictionSectionsComplex Λ Y kbar C ⟶
      frobeniusRestrictionSectionsComplex Λ Y kbar C :=
  Functor.twistChainEndo
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
    (frobeniusRestrictionTwist Λ Y kbar p q hcard C)

variable [IsFinite Y.hom]

omit [Fintype k] in
/-- For `Y` finite over `k`, perfectness of `RΓ(Y_k̄, C|_{Y_k̄})` is perfectness of the complex of
global sections `Γ(Spec k̄, pr_* (C|_{Y_k̄}))`. -/
lemma isPerfect_frobeniusRestrictionSectionsComplex_iff
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))) ↔
      StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj (frobeniusRestrictionSectionsComplex Λ Y kbar C).obj) :=
  Functor.isPerfect_twist_iff_of_exact _ _ _

/-- **For `Y` finite over `k` the trace of `π_Y^*` on `RΓ(Y_k̄, C|_{Y_k̄})` is computed on global
sections.**  Direct image to `Spec k̄` and global sections over `Spec k̄` are exact, so the derived
endomorphism is the termwise endomorphism of `Γ(Spec k̄, pr_* (C|_{Y_k̄}))`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_isFinite
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C))))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      perfectDerivedTrace Λ
        ⟨_, (isPerfect_frobeniusRestrictionSectionsComplex_iff Λ Y kbar C).1 hperf⟩
        (DerivedCategory.Q.map (frobeniusRestrictionSectionsEndo Λ Y kbar p q hcard C).hom) := by
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  exact Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_exact _ _ _ _ _ _ hperf

end Finite

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace

/-!
# Additivity of the trace of the canonical Frobenius action

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j : X ⟶ X̄` and `k̄` an
extension of `k`.  This file proves Step 1 of the proof of [Stacks, Tag 03UG] for the canonical
action `π_X^*` of `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`: along a short exact
sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of sheaves of `Λ`-modules on `X`,

`Tr(π_X^* | RΓ_c(X_k̄, K₂)) = Tr(π_X^* | RΓ_c(X_k̄, K₁)) + Tr(π_X^* | RΓ_c(X_k̄, K₃))`,

and perfectness of `RΓ_c(X_k̄, -)` is two out of three.  In the source this is applied to
`0 → j_!j^{-1}K → K → i_*i^{-1}K → 0` for an open `U ⊆ X` with closed complement.

## Main results

* `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo` — the canonical
  endomorphism is an instance of `CategoryTheory.Functor.derivedTwistEndo`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_X₂_eq_add` —
  additivity of the trace of the canonical endomorphism of `RΓ(Y_k̄, -)` on any `Y` over `k`.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_X₂_eq_add` — additivity of the
  trace.
* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_X₂` — two out of three for
  perfectness.

## Implementation notes

Extension by zero and inverse image along `X̄_k̄ ⟶ X̄` are exact, so they carry the short exact
sequence to one on `X̄_k̄`; the Frobenius base change twist is a natural transformation, so it
is a morphism of short complexes into the image of that sequence under `π̄_*`.  The abstract
statement `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add` then applies
verbatim, the canonical action being definitionally the derived endomorphism attached to that
twist.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The canonical endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})` is the derived endomorphism attached to
the twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` given by the Frobenius base change twist. -/
lemma frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C =
      Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app C.obj)) :=
  rfl

omit [Fintype k] in
/-- Restriction to `Y_k̄` preserves short exact sequences of complexes. -/
lemma fieldBaseChangeRestriction_shortExact
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)} (hS : S.ShortExact) :
    (S.map ((etaleModuleInverseImage.{u, r} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (fieldBaseChangeProj Y kbar)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ (fieldBaseChangeProj Y kbar)
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).map_of_exact _

/-- **Step 1 of the proof of [Stacks, Tag 03UG] on an arbitrary scheme over `k`.**  For a short
exact sequence `0 → C₁ → C₂ → C₃ → 0` of bounded below complexes of sheaves of `Λ`-modules on
`Y_étale` with `RΓ(Y_k̄, Cᵢ|_{Y_k̄})` perfect, the traces of the canonical endomorphisms
`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo` satisfy `Tr(C₂) = Tr(C₁) + Tr(C₃)`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_X₂_eq_add
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₁, h₁⟩)))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₂, h₂⟩)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₃, h₃⟩))))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₂, h₂⟩)) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₁, h₁⟩)) +
        CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₃⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₃, h₃⟩)) :=
  Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (fieldBaseChangeRestriction_shortExact.{u, r} Λ Y kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₁, h₁⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₂, h₂⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₃, h₃⟩).property)
    (ShortComplex.mapNatTrans S (NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ))) hp₁ hp₂ hp₃

end Frobenius

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The short complex of complexes on `X̄_k̄` obtained from a short complex of complexes on `X` by
extension by zero to the compactification `X̄` followed by restriction to `X̄_k̄`. -/
abbrev compactSupportShortComplex (S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)) :
    ShortComplex
      (CochainComplex (EtaleModules.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) ℤ) :=
  (S.map ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapHomologicalComplex _)).map
    ((etaleModuleInverseImage.{u, r} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _)

omit [Fintype k] in
/-- Extension by zero and restriction to `X̄_k̄` preserve short exact sequences of complexes. -/
lemma compactSupportShortComplex_shortExact
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact) :
    (compactSupportShortComplex.{u, r} Λ f j kbar S).ShortExact := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  have : PreservesFiniteColimits (etaleModuleExtensionByZero.{u, r} Λ j.immersion) :=
    let : (etaleModuleExtensionByZero.{u, r} Λ j.immersion).IsLeftAdjoint :=
      (etaleModuleExtensionByZeroAdj.{u, r} Λ j.immersion).isLeftAdjoint
    inferInstance
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  exact ((hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).map_of_exact
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion)).map_of_exact _

/-- The Frobenius twist of `compactSupportShortComplex`, componentwise the base change twist of
`Stacks.EtaleCohomology.frobeniusBaseChangeTwist`. -/
def compactSupportShortComplexTwist
    (S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)) :
    compactSupportShortComplex.{u, r} Λ f j kbar S ⟶
      (compactSupportShortComplex.{u, r} Λ f j kbar S).map
        ((etaleModuleDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapHomologicalComplex
            _) :=
  ShortComplex.mapNatTrans
    (S.map ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapHomologicalComplex _))
    (NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, r} Λ (Over.mk j.toBase) kbar p q hcard) (ComplexShape.up ℤ))

/-- **Step 1 of the proof of [Stacks, Tag 03UG]: the trace of `π_X^*` on `RΓ_c(X_k̄, -)` is
additive along short exact sequences.**  For a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of
bounded below complexes of sheaves of `Λ`-modules on `X_étale` with `RΓ_c(X_k̄, Kᵢ)` perfect,

`Tr(π_X^* | RΓ_c(X_k̄, K₂)) = Tr(π_X^* | RΓ_c(X_k̄, K₁)) + Tr(π_X^* | RΓ_c(X_k̄, K₃))`

in `Λ^natural`, for the canonical action of
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` through one compactification. -/
theorem canonicalCompactSupportLefschetzNumber_X₂_eq_add [Finite Λ]
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩)))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₂, h₂⟩)))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩))) :
    canonicalCompactSupportLefschetzNumber.{u, r} Λ f j kbar p q hcard ⟨S.X₂, h₂⟩ hp₂ =
      canonicalCompactSupportLefschetzNumber.{u, r} Λ f j kbar p q hcard ⟨S.X₁, h₁⟩ hp₁ +
        canonicalCompactSupportLefschetzNumber.{u, r} Λ f j kbar p q hcard ⟨S.X₃, h₃⟩ hp₃ :=
  Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    (compactSupportShortComplex_shortExact.{u, r} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₂, h₂⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₃, h₃⟩)).property)
    (compactSupportShortComplexTwist.{u, r} Λ f j kbar p q hcard S) hp₁ hp₂ hp₃

omit [Fintype k] in
/-- **Perfectness of `RΓ_c(X_k̄, -)` is two out of three along a short exact sequence.** -/
theorem isPerfect_compactSupportFrobeniusCohomology_X₂
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩)))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₂, h₂⟩)) :=
  Functor.isPerfect_twistDerivedObj_X₂.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (compactSupportShortComplex_shortExact.{u, r} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₂, h₂⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₃, h₃⟩)).property)
    hp₁ hp₃

end CompactSupport

end Stacks.EtaleCohomology

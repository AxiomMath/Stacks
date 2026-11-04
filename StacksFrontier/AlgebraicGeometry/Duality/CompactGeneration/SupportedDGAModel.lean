module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexLocalizingImage
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexCompactGeneratorEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexKInjectiveRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRepCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# A differential graded algebra model for `D_{QCoh,T}(𝒪_X)`

Let `X` be a quasi-compact and quasi-separated scheme and let `T ⊆ X` be a closed subset such that
`X ∖ T` is quasi-compact. [Stacks, Tag 0DJL] says that the analogue of [Stacks, Tag 09M5] holds for
`D_{QCoh,T}(𝒪_X)`: there is a differential graded algebra `(E, d)` with only finitely many nonzero
cohomology groups `H^i(E)` such that `D_{QCoh,T}(𝒪_X)` is equivalent to `D(E, d)`.

## Main definitions

* `Stacks.Duality.SupportedGeneration.quasiCoherentSupportedModelEquiv`: `D_{QCoh,T}(𝒪_X)` at one
  model of the derived category is equivalent to `D_{QCoh,T}(𝒪_X)` at any other.

## Main results

* `Stacks.Duality.SupportedGeneration.exists_generator_quasiCoherentSupported_standard`: the
  generator of Tag 0A9A at the standard model, compact in `D_{QCoh,T}(𝒪_X)`, with finitely many
  nonzero self-extensions.
* `exists_isKInjective_dga_equivalence_quasiCoherentSupported_standard`, in the namespace
  `Stacks.Duality.SupportedGeneration`: the equivalence of Tag 0DJL at the standard model, given
  by `- ⊗_E^𝐋 K` for a K-injective complex `K` with endomorphism differential graded algebra `E`.
* `Stacks.Duality.SupportedGeneration.exists_dga_equivalence_quasiCoherentSupported`: Tag 0DJL,
  `D_{QCoh,T}(𝒪_X) ≌ D(E, d)` for a differential graded algebra `(E, d)` with only finitely many
  nonzero cohomology groups.

## References

* [Stacks Project, Tag 0DJL](https://stacks.math.columbia.edu/tag/0DJL)
* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 0A9B](https://stacks.math.columbia.edu/tag/0A9B)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 09M3](https://stacks.math.columbia.edu/tag/09M3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open StacksDraft.DerivedModel

universe w z u

namespace Stacks.Duality.SupportedGeneration

/-! ### `D_{QCoh,T}(𝒪_X)` does not depend on the model of the derived category -/

section Model

variable (X : Scheme.{u}) (T : Set X)
  (h₁ : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf))
  (h₂ : HasDerivedCategory.{z} (SheafOfModules.{u} X.ringCatSheaf))

/-- **Membership in `D_{QCoh,T}(𝒪_X)` does not depend on the model of the derived category**: an
object lies in it exactly when its transport along `StacksDraft.DerivedModel.modelEquiv` does. -/
theorem quasiCoherentSupported_modelEquiv_functor_obj_iff (K : @DerivedCategory _ _ _ h₁) :
    @Stacks.Duality.quasiCoherentSupported X T h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @Stacks.Duality.quasiCoherentSupported X T h₁ K :=
  and_congr
    (derivedCategoryB_modelEquiv_functor_obj_iff (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      h₁ h₂ K)
    (derivedCategoryB_modelEquiv_functor_obj_iff (Stacks.Duality.supportedModules X.ringCatSheaf T)
      h₁ h₂ K)

/-- **`D_{QCoh,T}(𝒪_X)` at one model is equivalent to `D_{QCoh,T}(𝒪_X)` at any other**, by the
restriction of the comparison equivalence `StacksDraft.DerivedModel.modelEquiv`. -/
def quasiCoherentSupportedModelEquiv :
    @Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T h₁ ≌
      @Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T h₂ :=
  have := @Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderIsomorphisms X T h₂
  (modelEquiv h₁ h₂).congrFullSubcategory
    (funext fun K ↦ propext (quasiCoherentSupported_modelEquiv_functor_obj_iff X T h₁ h₂ K))

/-- The equivalence `quasiCoherentSupportedModelEquiv` is additive. -/
instance quasiCoherentSupportedModelEquiv_functor_additive :
    (quasiCoherentSupportedModelEquiv X T h₁ h₂).functor.Additive where
  map_add {_ _ f g} := by
    have := modelEquiv_functor_additive h₁ h₂
    exact ObjectProperty.hom_ext _ ((modelEquiv h₁ h₂).functor.map_add (f := f.hom) (g := g.hom))

end Model


/-! ### The generator at the standard model -/

section Standard

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (T : Set X)

/-- **The generator of [Stacks, Tag 0A9A] at the standard model of the derived category.** Let `X`
be quasi-compact and quasi-separated and `T ⊆ X` closed with `X ∖ T` quasi-compact. At the
standard model `AlgebraicGeometry.RingedSite.schemeStandardDerivedCategory X` there is an object
`G` of `D_{QCoh,T}(𝒪_X)` which

* is compact in `D_{QCoh,T}(𝒪_X)` ([Stacks, Tag 0A9B]),
* generates it: an object of `D(𝒪_X)` with quasi-coherent cohomology supported on `T` receiving
  no nonzero morphism from any shift of `G` is zero ([Stacks, Tag 0A9A]),
* has `Hom(G, G⟦n⟧) = 0` for all but finitely many `n` ([Stacks, Tag 09M4]). -/
theorem exists_generator_quasiCoherentSupported_standard (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set X)) :
    ∃ G : @Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T
        (RingedSite.schemeStandardDerivedCategory X),
      IsCompactObject.{u} G ∧
      (∀ L : @DerivedCategory _ _ _ (RingedSite.schemeStandardDerivedCategory X),
        @Stacks.Duality.quasiCoherentSupported X T (RingedSite.schemeStandardDerivedCategory X) L →
        (∀ (n : ℤ) (f : G.obj⟦n⟧ ⟶ L), f = 0) → IsZero L) ∧
      {n : ℤ | ¬ Subsingleton (G.obj ⟶ G.obj⟦n⟧)}.Finite := by
  obtain ⟨G₀, hGp, hGc, hGgen⟩ := exists_isPerfect_generator_quasiCoherentSupported X T hT hTc
  let hL : HasDerivedCategory.{u} (SheafOfModules.{u} X.ringCatSheaf) := inferInstance
  let hS := RingedSite.schemeStandardDerivedCategory X
  let E' := quasiCoherentSupportedModelEquiv X T hL hS
  let e := modelEquiv hL hS
  let : e.functor.CommShift ℤ := StacksDraft.Perfect.derivedEquivalenceCommShift _ _
  have := @Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderIsomorphisms X T hS
  have hG'p : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hS
      (e.functor.obj G₀.obj) := by
    let E := (@DerivedCategory.Q _ _ _ hL).objPreimage G₀.obj
    let e₁ := (@DerivedCategory.Q _ _ _ hL).objObjPreimageIso G₀.obj
    let e₂ : (@DerivedCategory.Q _ _ _ hS).obj E ≅ e.functor.obj G₀.obj :=
      ((modelCompQIso hL hS).app E).symm ≪≫ e.functor.mapIso e₁
    exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ _ e₁ e₂).1 hGp
  refine ⟨E'.functor.obj G₀, (isCompactObject_iff_isCompactObject_obj E'.functor G₀).1 hGc,
    fun L hLs hLf ↦ ?_, ?_⟩
  · let L₀ := e.inverse.obj L
    have hL₀ : @Stacks.Duality.quasiCoherentSupported X T hL L₀ :=
      (quasiCoherentSupported_modelEquiv_functor_obj_iff X T hL hS L₀).1
        ((Stacks.Duality.quasiCoherentSupported X T).prop_of_iso (e.counitIso.app L).symm hLs)
    have hz : IsZero L₀ := hGgen L₀ hL₀ fun n g ↦ by
      apply e.functor.map_injective
      rw [Functor.map_zero, ← cancel_epi ((e.functor.commShiftIso n).inv.app G₀.obj),
        ← cancel_mono (e.counitIso.hom.app L), Category.assoc, comp_zero, zero_comp]
      exact hLf n _
    exact (e.functor.map_isZero hz).of_iso (e.counitIso.app L).symm
  · let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) := hS
    obtain ⟨c, d, hc, hd⟩ :=
      Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect X
        (e.functor.obj G₀.obj) hG'p
    exact Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs X
      (e.functor.obj G₀.obj) hG'p (e.functor.obj G₀.obj) (E'.functor.obj G₀).property.1 c d hc hd

end Standard


/-! ### [Stacks, Tag 0DJL] -/

section Theorem

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (T : Set X)

/-- **The equivalence of [Stacks, Tag 0DJL] at the standard model.** For `X` quasi-compact and
quasi-separated and `T ⊆ X` closed with `X ∖ T` quasi-compact, there is a complex `K` of
`𝒪_X`-modules on the site of opens of `X` which is K-injective, whose endomorphism differential
graded algebra `(E, d) = Hom_{Comp^dg(𝒪_X)}(K, K)` has only finitely many nonzero cohomology
groups, and such that `D(E, d)` is equivalent to `D_{QCoh,T}(𝒪_X)`. The equivalence is
`- ⊗_E^𝐋 K` of Tag 09LX. -/
theorem exists_isKInjective_dga_equivalence_quasiCoherentSupported_standard (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set X)) :
    ∃ K : CochainComplex (RingedSite.ModO.{u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X)) ℤ,
      (RingedSite.liftComplex.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X) K).IsKInjective ∧
      {n : ℤ | Nontrivial ((RingedSite.Rep.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X) ℤ K).algebra.Cohomology
          n)}.Finite ∧
      Nonempty (@Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T
          (RingedSite.schemeStandardDerivedCategory X) ≌
        DifferentialGradedModule.derivedCategory.{0, u, u}
          (RingedSite.Rep.{u, u, u, u, u, 0}
            (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X) ℤ K).algebra) := by
  let Xs := Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X
  let hS := RingedSite.schemeStandardDerivedCategory X
  obtain ⟨G, hGc, hGgen, hGfin⟩ := exists_generator_quasiCoherentSupported_standard X T hT hTc
  obtain ⟨K, hKinj, ⟨eK'⟩⟩ := RingedSite.exists_isKInjective_liftComplex_iso Xs G.obj
  let eK : (@DerivedCategory.Q _ _ _ hS).obj (RingedSite.liftComplex.{u, u, u, u, u} Xs K) ≅
      G.obj := eK'
  have := hKinj
  let P := @Stacks.Duality.quasiCoherentSupported X T hS
  have : P.IsClosedUnderIsomorphisms :=
    @Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderIsomorphisms X T hS
  have : P.IsTriangulated := @Stacks.Duality.Supported.quasiCoherentSupported_isTriangulated X T hS
  have hKP : P ((@DerivedCategory.Q _ _ _ hS).obj (RingedSite.liftComplex.{u, u, u, u, u} Xs K)) :=
    P.prop_of_iso eK.symm G.property
  have hP := RingedSite.tensorWithComplexDerived_obj_quasiCoherentSupported_scheme X T K hKP
  have hsum : ∀ {ι : Type u} (Z : ι → @DerivedCategory _ _ _ hS) (c : Cofan Z), IsColimit c →
      (∀ i, P (Z i)) → P c.pt := fun {ι} Z c hc hZ ↦ by
    have := @Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderCoproducts X T hS ι
    exact P.prop_of_isColimit hc fun j ↦ hZ j.as
  have hcompact : IsCompactObject.{u}
      (⟨(@DerivedCategory.Q _ _ _ hS).obj (RingedSite.liftComplex.{u, u, u, u, u} Xs K), hKP⟩ :
        P.FullSubcategory) :=
    isCompactObject_of_iso (P.fullyFaithfulι.preimageIso eK) hGc
  have hgen : ∀ L : @DerivedCategory _ _ _ hS, P L →
      (∀ (n : ℤ) (f : ((@DerivedCategory.Q _ _ _ hS).obj
        (RingedSite.liftComplex.{u, u, u, u, u} Xs K))⟦n⟧ ⟶ L), f = 0) → IsZero L :=
    fun L hL hf ↦ hGgen L hL fun n f ↦ by
      rw [← cancel_epi ((shiftFunctor _ n).map eK.hom), comp_zero]
      exact hf n _
  have hfin : {n : ℤ | ¬ Subsingleton ((@DerivedCategory.Q _ _ _ hS).obj
      (RingedSite.liftComplex.{u, u, u, u, u} Xs K) ⟶
        ((@DerivedCategory.Q _ _ _ hS).obj
          (RingedSite.liftComplex.{u, u, u, u, u} Xs K))⟦n⟧)}.Finite :=
    hGfin.subset fun n ↦
      mt (Iso.homCongr eK ((shiftFunctor _ n).mapIso eK)).subsingleton_congr.2
  exact ⟨K, hKinj, RingedSite.finite_setOf_nontrivial_cohomology_rep.{u, u, u, u, u} Xs K hfin,
    ⟨@CategoryTheory.Equivalence.symm _ _ _ _
      (@RingedSite.tensorWithComplexDerivedLiftEquivalence.{u, u, u, u, u} Xs K P ‹_› ‹_› hKinj hP
        hsum hKP hcompact hgen)⟩⟩

/-- **[Stacks, Tag 0DJL].** *"Let `X` be a quasi-compact and quasi-separated scheme. Let
`T ⊂ X` be a closed subset such that `X ∖ T` is quasi-compact. The analogue of Theorem 09M5 holds
for `D_{QCoh,T}(𝒪_X)`."* That is: there is a differential graded algebra `(E, d)` with only a
finite number of nonzero cohomology groups `H^i(E)` such that `D_{QCoh,T}(𝒪_X)` is equivalent to
`D(E, d)`. The derived category of `𝒪_X`-modules is taken at an arbitrary model `h`. -/
@[stacks 0DJL]
theorem exists_dga_equivalence_quasiCoherentSupported (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set X))
    [h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)] :
    ∃ E : DifferentialGradedAlgebra.{0, u} ℤ, {i : ℤ | Nontrivial (E.Cohomology i)}.Finite ∧
      Nonempty (@Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T h ≌
        DifferentialGradedModule.derivedCategory.{0, u, u} E) := by
  obtain ⟨K, -, hfin, ⟨e⟩⟩ :=
    exists_isKInjective_dga_equivalence_quasiCoherentSupported_standard X T hT hTc
  exact ⟨_, hfin, ⟨(quasiCoherentSupportedModelEquiv X T h
    (RingedSite.schemeStandardDerivedCategory X)).trans e⟩⟩

end Theorem

end Stacks.Duality.SupportedGeneration

end

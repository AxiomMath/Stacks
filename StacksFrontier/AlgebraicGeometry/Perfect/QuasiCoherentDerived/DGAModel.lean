module

public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.BoundednessStandardModel
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexKInjectiveRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRepCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# A differential graded algebra model for `D_QCoh` of a quasi-compact quasi-separated scheme

[Stacks, Tag 09M5], after Bondal and van den Bergh: *for a quasi-compact and quasi-separated
scheme `X` there is a differential graded algebra `(E, d)` with only finitely many nonzero
cohomology groups `H^i(E)` such that `D_QCoh(O_X)` is equivalent to `D(E, d)`.*

## The proof

It is the source's. Let `K^•` be a K-injective complex of `O_X`-modules which is perfect and
generates `D_QCoh(O_X)`: a perfect generator exists by Tag 09IS, and a K-injective representative
of it by Tag 079P (`AlgebraicGeometry.RingedSite.exists_isKInjective_liftComplex_iso`). Let
`(E, d) = Hom_{Comp^dg(O_X)}(K^•, K^•)`.

* `H^n(E) = Ext^n(K^•, K^•)` since `K^•` is K-injective (equation 09M6,
  `AlgebraicGeometry.RingedSite.repCohomologyEquivDerivedHom`), and only finitely many of these
  are nonzero by Tag 09M4 (a perfect complex on a quasi-compact scheme is bounded).
* The functor `- ⊗_E^𝐋 K^• : D(E, d) ⥤ D(O_X)` of Tag 09LX lands in `D_QCoh(O_X)` by Tag 09M3,
  and is an equivalence onto it: this is
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator`
  (Tags 09LZ, 09LY and 09J1), fed with the compactness of `K^•` in `D_QCoh(O_X)` (Tag 09M1) and
  the generation of `D_QCoh(O_X)` by `K^•` (Tag 09IS).

## Main results

* `AlgebraicGeometry.exists_isKInjective_tensorWithComplexDerived_lift_isEquivalence`: the whole
  construction at the standard model of `D(O_X)`, keeping the complex `K^•`, the K-injectivity
  and the functor, for reuse.
* `AlgebraicGeometry.exists_differentialGradedAlgebra_quasiCoherentDerivedCategory_equivalence`:
  **Stacks 09M5**, for an arbitrary chosen model of the derived category.

## Implementation notes

The scheme is read as the ringed site of its opens,
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`, the shape in which the derived
tensor product of Tag 09LX is constructed; with all universes equal, its category of modules is
`X.Modules` itself. The derived category of Tag 09LX is the standard model; the statement of
Tag 09M5 is transported to an arbitrary model through
`StacksDraft.DerivedModel.derivedCategoryBModelEquiv`. The compactness of Tag 09M1 is proved in
this library at the locally small model and is transported the same way, at the fixed index
universe of the direct sums.

The differential graded algebra is an algebra over `ℤ`: the endomorphism algebra of a complex of
`O_X`-modules is an algebra of abelian groups. Its carrier lies in the universe of `X`, and so do
the differential graded modules of `D(E, d)`.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* A. Bondal, M. van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality.CompactBoundedness StacksDraft.DerivedModel

namespace AlgebraicGeometry

universe u

/-- `D_QCoh(O_X)` on the derived category of the ambient modules of the scheme read as a ringed
site, at the standard model. -/
abbrev qcohDerivedProperty (X : Scheme.{u}) :
    ObjectProperty (@DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X)) _ _
        (HasDerivedCategory.standard _)) :=
  @DerivedCategoryB.derivedCategoryB X.Modules _ _ (HasDerivedCategory.standard X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)

/-- Quasi-coherence of `O_X`-modules is a weak Serre property. -/
alias isWeakSerre_isQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre

/-- `D_QCoh(O_X)` at the standard model is closed under isomorphisms. -/
instance (X : Scheme.{u}) : (qcohDerivedProperty X).IsClosedUnderIsomorphisms :=
  @DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms X.Modules _ _
    (HasDerivedCategory.standard X.Modules) _ (isWeakSerre_isQuasicoherent X)

/-- `D_QCoh(O_X)` at the standard model is a triangulated subcategory. -/
instance (X : Scheme.{u}) : (qcohDerivedProperty X).IsTriangulated :=
  @DerivedCategoryB.derivedCategoryB_isTriangulated X.Modules _ _
    (HasDerivedCategory.standard X.Modules) _ (isWeakSerre_isQuasicoherent X)

/-- The scheme read as a ringed site. -/
local notation "𝒮" X => Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X

/-- The derived category of the ambient modules of the scheme read as a ringed site, at the
standard model: the model on which the derived tensor product of Tag 09LX is built. -/
abbrev stdDerived (X : Scheme.{u}) :=
  @DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X)) _ _ (HasDerivedCategory.standard _)

/-- The localization functor of `stdDerived`. -/
abbrev stdQ (X : Scheme.{u}) :
    CochainComplex (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X)) ℤ ⥤ stdDerived X :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- **Tag 09IS at `stdDerived`.** A quasi-compact quasi-separated scheme has a perfect object `G`
of `D(O_X)` generating `D_QCoh(O_X)`: an object `L` of `D_QCoh(O_X)` with `Hom(G[n], L) = 0` for
all `n` is zero. -/
theorem exists_isPerfect_generator_stdDerived (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ G : stdDerived X, IsPerfectStd (show Dstd X from G) ∧
      ∀ L : stdDerived X, qcohDerivedProperty X L →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ L), f = 0) → IsZero L :=
  Stacks.SheafOfModules.exists_isPerfect_generator_modules X

/-- **Tag 09M4 at `stdDerived`.** A perfect object `G` of `D(O_X)` on a quasi-compact
quasi-separated scheme has only finitely many nonzero `Ext^n(G, G)`: it is bounded, as `X` is
quasi-compact, and Tag 09M4 (2) applies with `L = G`. -/
theorem finite_setOf_not_subsingleton_stdDerived (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (G : stdDerived X) (hG : IsPerfectStd (show Dstd X from G)) :
    {n : ℤ | ¬ Subsingleton (G ⟶ G⟦n⟧)}.Finite := by
  obtain ⟨a, b, hGa, hGb⟩ :=
    @Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect X _
      (HasDerivedCategory.standard _) G hG
  exact Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs X G
    hG G (isQuasicoherent_of_isPerfectStd G hG) a b hGa hGb

/-- **Tag 09M1 at `stdDerived`.** A perfect object of `D(O_X)` on a quasi-compact
quasi-separated scheme is a compact object of `D_QCoh(O_X)`, for direct sums indexed by the
universe of `X`. Tag 09M1 is proved in this library at the locally small model; compactness at a
fixed index universe is carried across the comparison of the two models. -/
theorem isCompactObject_stdDerived (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G : stdDerived X) (hG : IsPerfectStd (show Dstd X from G))
    (hGP : qcohDerivedProperty X G) :
    IsCompactObject.{u} (⟨G, hGP⟩ : (qcohDerivedProperty X).FullSubcategory) := by
  change IsCompactObject.{u}
    (⟨G, hGP⟩ : @Stacks.Duality.quasiCoherentDerivedCategory X
      (HasDerivedCategory.standard X.Modules))
  let e := Stacks.Duality.StandardModel.quasiCoherentModelEquiv X
  have h₁ : IsCompactObject.{u} (e.functor.obj ⟨G, hGP⟩) :=
    Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X (e.functor.obj ⟨G, hGP⟩)
      (isPerfect_toLocallySmall G hG)
  have := modelEquiv_functor_additive (HasDerivedCategory.standard X.Modules)
    (Scheme.Modules.hasDerivedCategory X)
  have : (e.functor ⋙ (@DerivedCategoryB.derivedCategoryB X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι).Additive :=
    inferInstanceAs ((@DerivedCategoryB.derivedCategoryB X.Modules _ _
      (HasDerivedCategory.standard X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
      (modelEquiv (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X)).functor).Additive
  have : e.functor.Additive := Functor.additive_of_comp_faithful e.functor
    (@DerivedCategoryB.derivedCategoryB X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
  exact (isCompactObject_iff_isCompactObject_obj e.functor _).2 h₁

/-- **The construction of Tag 09M5, at the standard model.** For a quasi-compact quasi-separated
scheme `X` there is a complex `K` of `O_X`-modules, K-injective (as `liftComplex K`, the complex
the endomorphism algebra is formed from), whose endomorphism differential graded algebra
`E = Hom_{Comp^dg(O_X)}(K, K)` has only finitely many nonzero cohomology groups, and such that
`- ⊗_E^𝐋 K : D(E, d) ⥤ D(O_X)` of Tag 09LX lands in `D_QCoh(O_X)` and is an equivalence onto it.

This keeps the data of the source's proof — the complex, its K-injectivity and the functor — for
the consumers of the construction (Remark 09SU). -/
theorem exists_isKInjective_tensorWithComplexDerived_lift_isEquivalence (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ)
      (_ : (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K).IsKInjective),
      {i : ℤ | Nontrivial
        ((RingedSite.Rep.{u, u, u, u, u, 0} (𝒮 X) ℤ K).algebra.Cohomology i)}.Finite ∧
      ∃ hP : ∀ M, qcohDerivedProperty X
          ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (𝒮 X) ℤ K).obj M),
        ((qcohDerivedProperty X).lift _ hP).IsEquivalence := by
  obtain ⟨G, hGperf, hGgen⟩ := exists_isPerfect_generator_stdDerived X
  have hGP : qcohDerivedProperty X G := isQuasicoherent_of_isPerfectStd G hGperf
  -- the K-injective representative `K` of `G`
  obtain ⟨K, hKinj, ⟨eK⟩⟩ := RingedSite.exists_isKInjective_liftComplex_iso (𝒮 X) G
  refine ⟨K, hKinj, ?_⟩
  have hKP : qcohDerivedProperty X
      ((stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K)) :=
    (qcohDerivedProperty X).prop_of_iso eK.symm hGP
  -- Tag 09M3: the derived tensor product lands in `D_QCoh`
  have hKP' : RingedSite.tensorModOQuasicoherentDerived.{u, u, u, u, u} (𝒮 X)
      ((stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K)) := by
    rw [RingedSite.tensorModOQuasicoherentDerived,
      RingedSite.tensorModOQuasicoherent_schemeRingedSite_eq X]
    exact hKP
  have hP : ∀ M, qcohDerivedProperty X
      ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (𝒮 X) ℤ K).obj M) := fun M =>
    RingedSite.derivedCategoryB_isQuasicoherent_tensorWithComplexDerived_obj_scheme X K hKP' M
  refine ⟨?_, hP, ?_⟩
  · -- equation 09M6 and Tag 09M4: finitely many nonzero cohomology groups
    refine RingedSite.finite_setOf_nontrivial_cohomology_rep.{u, u, u, u, u} (𝒮 X) K
      ((finite_setOf_not_subsingleton_stdDerived X G hGperf).subset fun n hn => ?_)
    change ¬ Subsingleton _ at hn ⊢
    exact fun hs => hn
      ((Iso.homCongr eK ((CategoryTheory.shiftFunctor _ n).mapIso eK)).subsingleton_congr.2 hs)
  · -- the equivalence: Tags 09LZ, 09LY, 09J1, fed with Tags 09M1 and 09IS
    have hsum : ∀ {ι : Type u} (Z : ι → stdDerived X)
        (c : Cofan Z), IsColimit c → (∀ i, qcohDerivedProperty X (Z i)) →
          qcohDerivedProperty X c.pt := fun Z c hc hZ =>
      RingedSite.derivedCategoryB_prop_of_isColimit.{u, u, u, u, u} (𝒮 X)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) (isWeakSerre_isQuasicoherent X)
        (fun M hM => Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
          (fun i => hM i.as) (coproductIsCoproduct M)) Z c hc hZ
    have hcompact : IsCompactObject.{u}
        (⟨(stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K), hKP⟩ :
          (qcohDerivedProperty X).FullSubcategory) :=
      isCompactObject_of_iso ((qcohDerivedProperty X).fullyFaithfulι.preimageIso
        (X := ⟨_, hKP⟩) (Y := ⟨G, hGP⟩) eK) (isCompactObject_stdDerived X G hGperf hGP)
    have hgen : ∀ L : stdDerived X, qcohDerivedProperty X L →
        (∀ (n : ℤ) (f : ((stdQ X).obj
          (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K))⟦n⟧ ⟶ L), f = 0) → IsZero L := by
      intro L hL h
      refine hGgen L hL (fun n f => ?_)
      have h₀ := h n (((CategoryTheory.shiftFunctor _ n).mapIso eK).hom ≫ f)
      rw [← Iso.inv_hom_id_assoc ((CategoryTheory.shiftFunctor _ n).mapIso eK) f, h₀,
        comp_zero]
    exact RingedSite.tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator.{u, u, u,
      u, u} (𝒮 X) K (qcohDerivedProperty X) hP hsum hKP hcompact hgen

/-- **Stacks 09M5** (Bondal–van den Bergh). *Let `X` be a quasi-compact and quasi-separated
scheme. Then there exist a differential graded algebra `(E, d)` with only a finite number of
nonzero cohomology groups `H^i(E)` such that `D_QCoh(O_X)` is equivalent to `D(E, d)`.*

`D_QCoh(O_X)` is the full subcategory of the derived category of `O_X`-modules — at an arbitrary
chosen model — of the objects all of whose cohomology sheaves are quasi-coherent, and `D(E, d)` is
the derived category of differential graded `E`-modules. The algebra is an algebra over `ℤ`, the
endomorphism algebra `Hom_{Comp^dg(O_X)}(K^•, K^•)` of a K-injective perfect generator `K^•` of
`D_QCoh(O_X)`; the equivalence is the derived tensor product `- ⊗_E^𝐋 K^•` of Tag 09LX, see
`AlgebraicGeometry.exists_isKInjective_tensorWithComplexDerived_lift_isEquivalence`, followed by
the comparison of the standard model with the chosen one. -/
@[stacks 09M5]
theorem exists_differentialGradedAlgebra_quasiCoherentDerivedCategory_equivalence
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasDerivedCategory X.Modules] :
    ∃ E : DifferentialGradedAlgebra.{0, u} ℤ,
      {i : ℤ | Nontrivial (E.Cohomology i)}.Finite ∧
        Nonempty ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ≌
            DifferentialGradedModule.derivedCategory.{0, u, u} E) := by
  obtain ⟨K, _, hfin, hP, hequiv⟩ :=
    exists_isKInjective_tensorWithComplexDerived_lift_isEquivalence X
  exact ⟨_, hfin, ⟨(@derivedCategoryBModelEquiv X.Modules _ _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (isWeakSerre_isQuasicoherent X).isClosedUnderIsomorphisms inferInstance
      (HasDerivedCategory.standard X.Modules)).trans
    ((qcohDerivedProperty X).lift _ hP).asEquivalence.symm⟩⟩

end AlgebraicGeometry

end

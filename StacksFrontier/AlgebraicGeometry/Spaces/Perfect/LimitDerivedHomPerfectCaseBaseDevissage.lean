module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectStrictlyPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartSlicePerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomPerfectCaseAffineLeaf
public import StacksFrontier.CategoryTheory.PullbackData.LimitDerivedHomPerfectCaseBaseClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PredicateDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover

/-!
# The dévissage of the affine leaf of Stacks 09RI down to its structure sheaf

In Situation 09RH the conclusion of Stacks 09RI for a pair `(E₀, K₀)` follows from the colimit
statement on the base-changed system `U_i = X_i ×_{X₀} U` over the affine objects `u : U ⟶ X₀`
of the small étale site, for the first argument `Lu^*E₀` and every shift of it
(`AlgebraicGeometry.Space.DescentSituation.isColim_of_shiftedIsColim_affineBaseChange`).  That
hypothesis is `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`, and the class of first
arguments satisfying it is closed under isomorphism, shift, the three vertices of a
distinguished triangle, binary biproducts and direct summands.

This file carries out the dévissage those closure properties were proved for.  The statement
proved is that the colimit statement at every shift, at a *strictly perfect* complex of
`𝒪_U`-modules, follows from the single statement at the **structure sheaf** `𝒪_U`: the dévissage
of Stacks 08FL, in the form
`Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect`, needs exactly the
five closure properties that are now available — isomorphism, zero objects, split retracts,
finite biproducts and the middle vertex of a distinguished triangle — and its base case is the
structure sheaf placed in a degree, which the closure under shifts reduces to degree `0`.

A perfect object on an affine algebraic space does have a global strictly perfect model:
`AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_of_isPerfect` gives one on an affine
*represented* space, and étale restriction along an isomorphism transports it.  So the dévissage
applies to `Lu^*E₀` for `E₀` perfect, and the whole of clause (1) of Stacks 09RI — `E₀` perfect,
`K₀` in `D_QCoh(𝒪_{X₀})` — rests on the colimit statement for the pair `(𝒪_U, Lu^*K₀)` alone,
that is on the bijectivity of

`colim_i Hom_{D(𝒪_{U_i})}(𝒪_{U_i}, (Lu^*K₀)_i⟦n⟧) ⟶ Hom_{D(𝒪_U)}(𝒪_U, (Lu^*K₀)⟦n⟧)`.

That statement is **not** proved here and is carried as a hypothesis everywhere below; it is the
geometric input of the source — the affine case of Stacks 09RE read across the comparison of the
small étale and the Zariski site — and it is where the tag's two universe restrictions live.  No
`@[stacks 09RI]` attribute is placed: everything here is conditional on it.  The statement is
proved, for `Lu^*K₀` in `D_QCoh(𝒪_U)`, as
`AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_isQuasicoherentOnSite`
in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomPerfectQcohLeaf.lean`, where both
clauses of Stacks 09RI are proved at the tag's own hypotheses.

## Main results

* `AlgebraicGeometry.Space.shiftedIsColim_Q_obj_of_isStrictlyPerfect`: the dévissage — the
  colimit statement at every shift of a strictly perfect complex, from the statement at the
  structure sheaf.
* `AlgebraicGeometry.Space.shiftedIsColim_of_isStrictlyPerfect_iso`: the same for an object
  isomorphic to a strictly perfect complex.
* `AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_of_isPerfect_of_isAffineSpace`: a perfect
  object on an affine algebraic space has a global strictly perfect model.
* `AlgebraicGeometry.Space.shiftedIsColim_of_isPerfect`: the dévissage for a perfect first
  argument over an affine base.
* `AlgebraicGeometry.Space.DescentSituation.isColim_of_structureSheafAffineBaseChange`:
  **Stacks 09RI, clause (1), reduced to the colimit statement at the structure sheaf** — the
  conclusion of the tag for `E₀` perfect and an arbitrary `K₀`, from the leaf statement for the
  pairs `(𝒪_U, Lu^*K₀)` over the affine objects étale over `X₀` and nothing else.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits etaleModuleLowerShriek_additive
  preservesFiniteLimits_etaleModuleLowerShriek preservesFiniteColimits_etaleModuleLowerShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V : AlgebraicSpaces B S hS} {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]

/-- **The dévissage of the affine leaf of Stacks 09RI.**  Let `Sys` be a directed system of
algebraic spaces over `V` with a cone and let `K` be an object of `D(𝒪_V)`.  If

`colim_j Hom_{D(𝒪_{V_j})}(𝒪_{V_j}, K_j⟦n⟧) ⟶ Hom_{D(𝒪_{V_∞})}(𝒪_{V_∞}, K_∞⟦n⟧)`

is bijective for every `n`, then the same holds with `𝒪_V` replaced by any strictly perfect
complex of `𝒪_V`-modules.

This is the dévissage of Stacks 08FL for the predicate
`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`, whose five closure properties are
`of_iso`, `of_isZero`, `of_retract`, `biproduct` and `obj₂`.  The base case of that dévissage is
the structure sheaf placed in a degree `i`, and `ShiftedIsColim` is quantified over the shifts,
so the hypothesis at degree `0` gives it at every degree. -/
theorem shiftedIsColim_Q_obj_of_isStrictlyPerfect
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) V J)
    (K : derivedModules B S hS V)
    (hunit : PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
        (SheafOfModules.unit _)) K)
    (Pcx : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ)
    (hPcx : IsStrictlyPerfect.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS V.1 V.2).O) Pcx) :
    PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS)
      (DerivedCategory.Q.obj Pcx) K := by
  have hcoh := smallEtaleDerivedPullbackData_isCoherent B S hS
  exact Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect
    (smallEtaleRingedSite B S hS V.1 V.2).O
    (fun E => PullbackData.LimitSystem.ShiftedIsColim Sys
      (smallEtaleDerivedPullbackData B S hS) E K)
    (fun _ _ e h => h.of_iso hcoh e)
    (fun _ hA => PullbackData.LimitSystem.ShiftedIsColim.of_isZero hA)
    (fun _ _ i r hr h => h.of_retract hcoh ⟨i, r, hr⟩)
    (fun f _ h => PullbackData.LimitSystem.ShiftedIsColim.biproduct hcoh f K h)
    (fun tri hT h₁ h₃ => PullbackData.LimitSystem.ShiftedIsColim.obj₂ hcoh tri hT K h₁ h₃)
    Pcx hPcx fun i _ => PullbackData.LimitSystem.ShiftedIsColim.of_shift hcoh i
      (hunit.of_iso hcoh (((DerivedCategory.singleFunctors
        (Modules.{u, u} B S hS V.1 V.2)).shiftIso i 0 i (add_zero i)).app
          (SheafOfModules.unit _)).symm)

/-- **The dévissage of the affine leaf of Stacks 09RI, for an object with a global strictly
perfect model.**  The colimit statement at every shift holds for any object of `D(𝒪_V)`
isomorphic to a strictly perfect complex, as soon as it holds for the structure sheaf. -/
theorem shiftedIsColim_of_isStrictlyPerfect_iso
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) V J)
    (K E : derivedModules B S hS V)
    (hunit : PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
        (SheafOfModules.unit _)) K)
    (hE : ∃ Pcx : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V.1 V.2).O) Pcx ∧
      Nonempty (E ≅ DerivedCategory.Q.obj Pcx)) :
    PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS) E K := by
  obtain ⟨Pcx, hPcx, ⟨e⟩⟩ := hE
  exact (shiftedIsColim_Q_obj_of_isStrictlyPerfect Sys K hunit Pcx hPcx).of_iso
    (smallEtaleDerivedPullbackData_isCoherent B S hS) e.symm

section Transport

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **A perfect object on an affine algebraic space has a global strictly perfect model.**  This
is `AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_of_isPerfect`, which is stated for the
algebraic space represented by an object of the site with affine underlying scheme, transported
along an isomorphism `V ≅ h_T`: étale restriction along an isomorphism preserves perfectness and
carries the structure sheaf to the structure sheaf, hence carries strictly perfect complexes to
strictly perfect complexes. -/
theorem exists_isStrictlyPerfect_iso_of_isPerfect_of_isAffineSpace
    (hV : IsAffineSpace B S hS V.1) (E : derivedModules B S hS V)
    (hE : (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect E) :
    ∃ Pcx : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V.1 V.2).O) Pcx ∧
      Nonempty (E ≅ DerivedCategory.Q.obj Pcx) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := hV
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let g : V ≅ W := ObjectProperty.isoMk _ eT
  let gh : V ⟶ W := g.hom
  let gi : W ⟶ V := g.inv
  have _ : IsIso gh.hom := inferInstanceAs (IsIso eT.hom)
  have _ : IsIso gi.hom := inferInstanceAs (IsIso eT.inv)
  have hgh : IsEtale B S hS gh.hom := isEtale_of_isIso B S hS gh.hom
  have hgi : IsEtale B S hS gi.hom := isEtale_of_isIso B S hS gi.hom
  let Li := etaleModulePullback.{u, u} B S hS gi hgi
  let Lh := etaleModulePullback.{u, u} B S hS gh hgh
  have _ : Li.Additive := etaleModulePullback_additive B S hS _ _
  have _ : PreservesFiniteLimits Li := preservesFiniteLimits_etaleModulePullback B S hS _ _
  have _ : PreservesFiniteColimits Li := preservesFiniteColimits_etaleModulePullback B S hS _ _
  have _ : Lh.Additive := etaleModulePullback_additive B S hS _ _
  have _ : PreservesFiniteLimits Lh := preservesFiniteLimits_etaleModulePullback B S hS _ _
  have _ : PreservesFiniteColimits Lh := preservesFiniteColimits_etaleModulePullback B S hS _ _
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isStrictlyPerfect_iso_of_isPerfect B S hS T
    (Li.mapDerivedCategory.obj E) (isPerfect_etaleModulePullback B S hS V gi hgi E hE)
  refine ⟨(Lh.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    SheafOfModules.isStrictlyPerfect_map _ (etaleModulePullbackUnitIso B S hS W gh hgh) hP, ⟨?_⟩⟩
  exact ((Stacks.DerivedGlueing.mapDerivedCategoryEquivalence Lh Li
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).unitIso
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).counitIso).counitIso.app E).symm ≪≫
    Lh.mapDerivedCategory.mapIso e ≪≫ Lh.mapDerivedCategoryFactors.app P

/-- **The dévissage of the affine leaf of Stacks 09RI, for a perfect first argument.**  On an
affine algebraic space `V` the colimit statement at every shift holds for every perfect object of
`D(𝒪_V)` as soon as it holds for the structure sheaf: a perfect object on an affine algebraic
space has a global strictly perfect model. -/
theorem shiftedIsColim_of_isPerfect
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) V J)
    (K E : derivedModules B S hS V) (hV : IsAffineSpace B S hS V.1)
    (hE : (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect E)
    (hunit : PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
        (SheafOfModules.unit _)) K) :
    PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS) E K :=
  shiftedIsColim_of_isStrictlyPerfect_iso Sys K E hunit
    (exists_isStrictlyPerfect_iso_of_isPerfect_of_isAffineSpace hV E hE)

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Stacks 09RI, clause (1), reduced to the colimit statement at the structure sheaf.**  In
Situation 09RH let `E₀` be a *perfect* object of `D(𝒪_{X₀})` and `K₀` any object of `D(𝒪_{X₀})`.
If for every étale `u : U ⟶ X₀` with `U` affine and every `n` the map

`colim_{i ≥ 0} Hom_{D(𝒪_{U_i})}(𝒪_{U_i}, (Lu^*K₀)_i⟦n⟧) ⟶ Hom_{D(𝒪_U)}(𝒪_U, (Lu^*K₀)⟦n⟧)`

is bijective, `U_i = X_i ×_{X₀} U`, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective.

Nothing is assumed about `K₀`; in the tag it lies in `D_QCoh(𝒪_{X₀})`, and that is where the
hypothesis `hunit` comes from in the source.  `hunit` is the whole of what clause (1) still
needs: the dévissage above turns it into the leaf statement for `Lu^*E₀`, which is perfect
(Stacks 08G5), and `isColim_of_shiftedIsColim_affineBaseChange` turns that into the conclusion of
the tag. -/
theorem isColim_of_structureSheafAffineBaseChange
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hE₀ : (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect E₀)
    (hunit : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (_hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
          (smallEtaleDerivedPullbackData B S hS)
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
            (SheafOfModules.unit _))
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ := by
  have _ : Nonempty D.Stages := ⟨⟨D.base, le_refl _⟩⟩
  exact isColim_of_shiftedIsColim_affineBaseChange E₀ K₀ fun u hu hV =>
    shiftedIsColim_of_isPerfect (baseChangeSystem u) _ _ hV
      (isPerfect_etaleModulePullback B S hS (D.stage D.base) u hu E₀ hE₀) (hunit u hu hV)

end DescentSituation

end Transport

end AlgebraicGeometry.Space

end

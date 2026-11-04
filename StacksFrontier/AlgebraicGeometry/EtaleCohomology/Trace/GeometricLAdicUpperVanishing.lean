module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Hⁱ_c(X_k̄, F)` vanishes above `2 dim X`, with no perfectness input

Let `X` be a separated scheme of finite type over a finite field `k`, let `k̄` be an algebraically
closed extension of `k` and `F = {Fₙ}` an ℓ-adic sheaf on `X`. Then
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = 0` for `i > 2 dim X`: the upper half of the degree bound of
[Stacks, Tag 03V2]. For a curve this is the vanishing of `Hⁱ_c` above degree two.

Unlike `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le`
no perfectness of the complexes `RΓ_c(X_k̄, Fₙ)` is used: every level `Hⁱ_c(X_k̄, Fₙ)` vanishes
already, so the limit does. A level is the cohomology on the proper scheme `X̄_k̄` of the torsion
sheaf `(j_! Fₙ)|_{X̄_k̄}`, which is zero away from `X_k̄`; the bound is
`Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint` with the
absolute case of [Stacks, Tag 095U], which the library proves
(`Stacks.EtaleCohomology.properDirectImageVanishingStatement`).

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le`:
  `Hⁱ_c(X_k̄, G) = 0` for `i > 2 dim X` and every sheaf `G` of `ℤ/mℤ`-modules, `m ≠ 0`.
* `LAdicSheaf.isZero_geometricCompactlySupportedCohomology_of_topologicalKrullDim_le` and
  `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt`: the same for
  `Hⁱ_c(X_k̄, F)` and `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)`.
* `LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt`:
  `Hⁱ_c(U_k̄, F ⊗ Q_ℓ) = 0` for `i > 2` on a smooth curve `U`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **The underlying abelian sheaf of `(j_! M)|_{X̄_k̄}` vanishes on every open subscheme of
`X̄_k̄` disjoint from `X_k̄`**: `(j_! M)|_{X̄_k̄}` is the extension by zero of `M|_{X_k̄}` along
the base-changed open immersion, and restriction to an open subscheme computes sections. -/
theorem isZero_etaleRestriction_underlyingAbelian_fieldBaseChange_extensionByZero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    {Λ : Type} [CommRing Λ] (M : EtaleModules.{u, 0} Λ X)
    {V : Scheme.{u}} (v : V ⟶ pullback j.toBase (specAlgebraMap k kbar)) [IsOpenImmersion v]
    (hv : Disjoint (Set.range v)
      (Set.range (compactificationFieldBaseChangeImmersion f j kbar))) :
    IsZero ((etaleRestriction.{u, 0} v).obj
      ((etaleModuleUnderlyingAbelian _ Λ).obj
        ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj M)))) := by
  have h0 : IsZero ((etaleModuleRestriction.{u, 0} Λ v).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M))) := by
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ v).app _).symm
    refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, 0} Λ v).mapIso
      ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app M).symm)
    exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ v
      (compactificationFieldBaseChangeImmersion f j kbar) hv _
  refine isZero_of_forall_isZero_sections.{u, 0} _ fun W ↦ ?_
  have hW := ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W)).map_isZero h0)
  change IsZero ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
    (_ : ModuleCat.{u + 1} Λ))
  exact (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_isZero hW

section Level

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

/-- `RΓ_c(X_k̄, G)` of a sheaf placed in degree zero is `RΓ(Spec k̄, Rg_* (j_! G)|_{X̄_k̄})`. -/
def compactSupportFrobeniusCohomologySingleIso {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ X) :
    DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩) ≅
      derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ
        ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj G)) :=
  DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} _
    (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} _
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
      ((DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, 0} _
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
          (ObjectProperty.isoMk _
            (Y := ⟨(CochainComplex.singleFunctor _ 0).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj G),
              CochainComplex.plus_singleFunctor_obj _⟩)
            ((HomologicalComplex.singleMapHomologicalComplex
              (etaleModuleExtensionByZero.{u, 0} _ j.immersion) (ComplexShape.up ℤ) 0).app G)))) ≪≫
        fieldBaseChangeRestrictionSingleIso (Over.mk j.toBase) kbar
          ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj G))))

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, G) = 0` for `i > 2 dim X`**, for every sheaf `G` of `ℤ/mℤ`-modules with
`m ≠ 0` on `X_étale`: the cohomology on the proper scheme `X̄_k̄` of the torsion sheaf
`(j_! G)|_{X̄_k̄}`, supported on `X_k̄`, vanishes above `2 dim X_k̄` by Tag 095U, and
`dim X_k̄ ≤ dim X`. -/
@[sga "4½ Arcata 4.6.1" "special case"]
theorem isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le
    (m : ℕ) [NeZero m] (G : EtaleModules.{u, 0} (ZMod m) X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (i : ℤ) (hi : 2 * (d : ℤ) < i) :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod m) f j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩ i) := by
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, i = q' := ⟨i.toNat, by omega⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (q' : ℤ)).mapIso
    (compactSupportFrobeniusCohomologySingleIso f j kbar G))
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (ZMod m) _ _ q' ?_
  have : QuasiCompact (pullback.snd f (specAlgebraMap k kbar)) := inferInstance
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) := by
    rw [compactificationFieldBaseChange_immersion_comp_snd]
    infer_instance
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar) :=
    QuasiCompact.of_comp _ (pullback.snd j.toBase (specAlgebraMap k kbar))
  have hXk : topologicalKrullDim ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) ≤ d :=
    topologicalKrullDim_pullback_le_of_fiber f d
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans hdim) _
  exact subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement) kbar
    (pullback.snd j.toBase (specAlgebraMap k kbar))
    (compactificationFieldBaseChangeImmersion f j kbar)
    d hXk _ (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod m _)
    (fun v _ hv ↦ isZero_etaleRestriction_underlyingAbelian_fieldBaseChange_extensionByZero f j
      kbar _ v hv) q' (by omega)

end Level

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, Fₙ)` with `ℤ_ℓ`-coefficients vanishes above `2 dim X`**, at every level of
an ℓ-adic sheaf: it is the restriction of scalars of `Hⁱ_c(X_k̄, Fₙ)` with
`ℤ/ℓⁿ⁺¹ℤ`-coefficients. -/
theorem LAdicSheaf.isZero_geometricCompactlySupportedCohomologySystem_obj_of_topologicalKrullDim_le
    [Finite k] (F : LAdicSheaf B X ℓ) (d : ℕ) (hdim : topologicalKrullDim X.1 ≤ d) (i : ℤ)
    (hi : 2 * (d : ℤ) < i) (n : ℕ) :
    IsZero ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj
      (op n)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have h := isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le f j
    kbar (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B X ℓ F n) d hdim i hi
  exact ((ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map_isZero h).of_iso
    ((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i).symm)

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, F) = 0` for `i > 2 dim X`**: a limit of zero modules. -/
theorem LAdicSheaf.isZero_geometricCompactlySupportedCohomology_of_topologicalKrullDim_le [Finite k]
    (F : LAdicSheaf B X ℓ) (d : ℕ) (hdim : topologicalKrullDim X.1 ≤ d) (i : ℤ)
    (hi : 2 * (d : ℤ) < i) :
    IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n =>
    (LAdicSheaf.isZero_geometricCompactlySupportedCohomologySystem_obj_of_topologicalKrullDim_le
      B X ℓ f j kbar F d hdim i hi n.unop).eq_of_tgt _ _)

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = 0` for `i > 2 dim X`**, the upper half of the degree bound of
[Stacks, Tag 03V2], for every ℓ-adic sheaf `F` on a separated scheme `X` of finite type over a
finite field, every algebraically closed extension `k̄` and every compactification, with no
perfectness or finiteness input: every level vanishes. For a curve (`d = 1`) this is
`Hⁱ_c = 0` for `i > 2`. -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt [Finite k]
    (F : LAdicSheaf B X ℓ) (d : ℕ) (hdim : topologicalKrullDim X.1 ≤ d) (i : ℤ)
    (hi : 2 * (d : ℤ) < i) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  Functor.map_isZero _
    (LAdicSheaf.isZero_geometricCompactlySupportedCohomology_of_topologicalKrullDim_le
      B X ℓ f j kbar F d hdim i hi)

omit [Fintype k] [IsSeparated f] [IsAlgClosed kbar] in
/-- **`Hⁱ_c(U_k̄, F ⊗ Q_ℓ) = 0` for `i > 2` on a curve**: for `U` smooth of relative dimension one
over a finite field `k`, an algebraic closure `k̄` of `k`, every ℓ-adic sheaf `F` on `U` and every
compactification. `U` has dimension at most one. -/
theorem LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt [Finite k]
    [SmoothOfRelativeDimension 1 f] [IsAlgClosure k kbar] (F : LAdicSheaf B X ℓ) (i : ℤ)
    (hi : 2 < i) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hdim : topologicalKrullDim X.1 ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rcases isEmpty_or_nonempty X.1 with hX | hX
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hX]
      exact bot_le
    · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  exact ModuleCat.subsingleton_of_isZero
    (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt B X ℓ f j kbar
      F 1 hdim i (by omega))

end Stacks.EtaleCohomology

end

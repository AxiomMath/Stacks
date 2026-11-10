module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTorsionFree

/-!
# Perfectness of `RΓ_c(X_k̄, F)` for a flat sheaf of `ℤ/pᵐℤ`-modules

Let `X` be a separated scheme of finite type over a finite field `k`, of dimension at most `d`,
with a compactification `j : X ⟶ X̄`, and let `F` be a flat (pow-exact) sheaf of `ℤ/pᵐℤ`-modules on
`X_étale`. The complex `RΓ_c(X_k̄, F)` is perfect as soon as the cohomology on `X̄_k̄` of the
reduction `((j_! F)|_{X̄_k̄})[p]` is finite: its vanishing above `2d` holds unconditionally, by
[Stacks, Tag 095U].

This gives the perfectness assertion of [Stacks, Tag 03V3] for the levels of the torsion-free
model of an `ℓ`-adic sheaf, with the finiteness of the cohomology of the reduction as a
hypothesis.

## Main results

* `isZero_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le`:
  `Hⁱ(X̄_k̄, ((j_! F)|_{X̄_k̄})[p]) = 0` for `i > 2d`.
* `isPerfect_compactSupportFrobeniusCohomology_single_of_powExact` and
  `..._of_finite`: `RΓ_c(X_k̄, F)` is perfect, granted finiteness of the cohomology of the
  reduction.
* `LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_finite`:
  the same for the levels of the torsion-free model of an `ℓ`-adic sheaf.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsAlgClosed kbar] in
/-- The reduction `((j_! F)|_{X̄_k̄})[p]` vanishes on every open of `X̄_k̄` disjoint from
`X_k̄`. -/
theorem isZero_etaleRestriction_underlyingAbelian_reduction_fieldBaseChange_extensionByZero
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X)
    {V : Scheme.{u}} (v : V ⟶ pullback j.toBase (specAlgebraMap k kbar)) [IsOpenImmersion v]
    (hv : Disjoint (Set.range v)
      (Set.range (compactificationFieldBaseChangeImmersion f j kbar))) :
    IsZero ((etaleRestriction.{u, 0} v).obj
      ((etaleModuleUnderlyingAbelian _ (ZMod p)).obj
        ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))) := by
  have h0 : IsZero ((etaleModuleRestriction.{u, 0} (ZMod (p ^ m)) v).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod (p ^ m))
        (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j.immersion).obj F))) := by
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, 0} _ v).app _).symm
    refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, 0} _ v).mapIso
      ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} _ f j kbar).app F).symm)
    exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint _ v
      (compactificationFieldBaseChangeImmersion f j kbar) hv _
  refine isZero_of_forall_isZero_sections.{u, 0} _ fun W ↦ ?_
  have hW := ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W)).map_isZero h0)
  change IsZero ((forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1}).obj
    ((ModuleCat.coextendScalars (torsionCoeff p m)).obj (_ : ModuleCat.{u + 1} (ZMod (p ^ m)))))
  exact (forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1}).map_isZero
    ((ModuleCat.coextendScalars (torsionCoeff p m)).map_isZero hW)

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ(X̄_k̄, ((j_! F)|_{X̄_k̄})[p]) = 0` for `i > 2 dim X`.** -/
theorem isZero_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (i : ℤ) (hi : 2 * (d : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))) := by
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, i = q' := ⟨i.toNat, by omega⟩
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (ZMod p) _ _ q' ?_
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
    d hXk _ (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod p _)
    (fun v _ hv ↦
      isZero_etaleRestriction_underlyingAbelian_reduction_fieldBaseChange_extensionByZero
        f j kbar p m F v hv) q' (by omega)

omit [Fintype k] [IsSeparated f] in
/-- **Perfectness of `RΓ_c(X_k̄, F)` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules** on a scheme of
dimension at most `d`, granted that the cohomology of the reduction `((j_! F)|_{X̄_k̄})[p]` is
finite. -/
theorem isPerfect_compactSupportFrobeniusCohomology_single_of_powExact
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : PowExact p m F) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (hf : ∀ i, Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F)))))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (p ^ m)) f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) :=
  isPerfect_compactSupportFrobeniusCohomology_single_of_reduction f j kbar p m F hF (2 * d)
    (fun i hi ↦ isZero_homology_derivedDirectImageSections_reduction_of_topologicalKrullDim_le
      f j kbar p m F d hdim i hi) hf

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include j in
/-- A scheme with a compactification over a field has finite dimension. -/
theorem exists_topologicalKrullDim_le_of_compactification :
    ∃ d : ℕ, topologicalKrullDim X ≤ d := by
  by_cases hX : IsEmpty X
  · exact ⟨0, by rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hX]; exact bot_le⟩
  · rw [not_isEmpty_iff] at hX
    have : IsProper j.toBase := j.property.2
    have hne : Nonempty (j.obj.right.left : Scheme.{u}) := ⟨j.immersion hX.some⟩
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper k j.toBase hne
    exact ⟨d, hd ▸ j.immersion.isOpenEmbedding.isInducing.topologicalKrullDim_le⟩

omit [Fintype k] [IsSeparated f] in
/-- **Perfectness of `RΓ_c(X_k̄, F)` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules**, granted that the
cohomology of the reduction `((j_! F)|_{X̄_k̄})[p]` is finite. -/
theorem isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_finite
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : PowExact p m F)
    (hf : ∀ i, Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F)))))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (p ^ m)) f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) :=
  have ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_compactification f j
  isPerfect_compactSupportFrobeniusCohomology_single_of_powExact f j kbar p m F hF d hd hf

section LAdic

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

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

omit [Fintype k] [IsSeparated f] in
/-- **The complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` of the torsion-free model of an `ℓ`-adic sheaf are
perfect**, granted that the cohomology of the reductions `((j_! F'ₙ)|_{X̄_k̄})[ℓ]` is finite. -/
theorem LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_finite
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hf : ∀ (n : ℕ) (i : ℤ), Module.Finite (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
                (LAdicSheaf.etaleLevel B X ℓ (model F) n))))))) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))) :=
  isPerfect_compactSupportFrobeniusCohomology_single_of_powExact_of_finite f j kbar ℓ (n + 1)
    (LAdicSheaf.etaleLevel B X ℓ (model F) n)
    (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl n) (hf n)

end LAdic

end Stacks.EtaleCohomology

end

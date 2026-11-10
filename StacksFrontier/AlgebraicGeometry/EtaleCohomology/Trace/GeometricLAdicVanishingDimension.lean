module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingSupport
public import StacksFrontier.AlgebraicGeometry.ClosurePointDimension.Basic

/-!
# `Hⁱ_c(X_k̄, F)` vanishes above `2 dim X`

The degree bound of [Stacks, Tag 03V2]: for a separated scheme `X` of finite type over a finite
field `k` and a `ℚ_ℓ`-sheaf `F` on `X`, `Hⁱ_c(X_k̄, F) = 0` for `i > 2 dim X`. The input is the
absolute case of [Stacks, Tag 095U] over the algebraically closed field `k̄`
(`ProperSeparablyClosedSheafHVanishingStatement`), together with the perfectness of the
complexes `RΓ_c(X_k̄, F'ₙ)` of the torsion-free model `F'` of `F`.

By `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_perfect_of_reduction` it
suffices to bound the cohomology on `X̄_k̄` of the reduction modulo `ℓ` of `(j_! F'ₙ)|_{X̄_k̄}`,
for a compactification `j : X ⟶ X̄`. That sheaf is the extension by zero from `X_k̄`
(`Stacks.EtaleCohomology.compactificationFieldBaseChangeExtensionByZeroIso`, [Stacks, Tag 03S6]),
so it vanishes on every open subscheme of `X̄_k̄` disjoint from `X_k̄`. The bound
`Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint` then gives
vanishing above `2 dim X_k̄`, and `dim X_k̄ ≤ dim X`: the fibres of `X_k̄ ⟶ Spec k̄` are fibres of
`X ⟶ Spec k`, which is `X` itself
(`Stacks.EtaleCohomology.topologicalKrullDim_pullback_le_of_fiber`).

Unlike `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_dim_le`, the bound is
in terms of the dimension of `X`, as in the source, not of its compactification.

## Main results

* `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le`
* `LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_isEmpty`
* `LAdicSheaf.nontrivial_rationalGeometricCompactlySupportedCohomology_bounds`:
  `Hⁱ_c(X_k̄, F) ≠ 0` only for `0 ≤ i ≤ 2 dim X`.

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

/-- **The reduction modulo `ℓ` of `(j_! M)|_{X̄_k̄}` vanishes on every open subscheme of `X̄_k̄`
disjoint from `X_k̄`**: `(j_! M)|_{X̄_k̄}` is the extension by zero of `M|_{X_k̄}` along the
base-changed open immersion, and restriction to an open subscheme computes sections, on which the
reduction is applied. -/
theorem isZero_etaleRestriction_coextendScalars_fieldBaseChange_extensionByZero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (M : EtaleModules.{u, 0} Λ X)
    {V : Scheme.{u}} (v : V ⟶ pullback j.toBase (specAlgebraMap k kbar)) [IsOpenImmersion v]
    (hv : Disjoint (Set.range v)
      (Set.range (compactificationFieldBaseChangeImmersion f j kbar))) :
    IsZero ((etaleRestriction.{u, 0} v).obj
      ((etaleModuleUnderlyingAbelian _ Λ').obj ((etaleModuleCoextendScalars ρ _).obj
        ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj M))))) := by
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
  change IsZero ((forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat.{u + 1}).obj
    ((ModuleCat.coextendScalars ρ).obj (_ : ModuleCat.{u + 1} Λ)))
  exact (forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat.{u + 1}).map_isZero
    ((ModuleCat.coextendScalars ρ).map_isZero hW)

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
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

omit [IsSeparated f] [CharP kbar p] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes above `2 dim X`**, the degree bound of [Stacks, Tag 03V2],
given the perfectness of the complexes `RΓ_c(X_k̄, F'ₙ)` of the torsion-free model and the
absolute case of [Stacks, Tag 095U] over the algebraically closed field `k̄`
(`ProperSeparablyClosedSheafHVanishingStatement`). -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le
    (h095U : ProperSeparablyClosedSheafHVanishingStatement.{u}) (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n)))) (d : ℕ)
    (hdim : topologicalKrullDim X.1 ≤ d) (i : ℤ) (hi : 2 * (d : ℤ) < i) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_perfect_of_reduction
    B X ℓ f j kbar p q hcard F hP (2 * d) (fun n i' hi' ↦ ?_) i hi
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, i' = q' := ⟨i'.toNat, by omega⟩
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (ZMod ℓ) _ _ q' ?_
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
  exact subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint h095U kbar
    (pullback.snd j.toBase (specAlgebraMap k kbar))
    (compactificationFieldBaseChangeImmersion f j kbar)
    d hXk _ (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod ℓ _)
    (fun v _ hv ↦ isZero_etaleRestriction_coextendScalars_fieldBaseChange_extensionByZero f j kbar
      _ _ v hv) q' (by omega)

omit [LocallyOfFiniteType f] [IsSeparated f] [CharP kbar p] [IsAlgClosed kbar] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes in every degree when `X` is empty**, given the perfectness of
the complexes `RΓ_c(X_k̄, F'ₙ)` of the torsion-free model: the extension by zero from the empty
scheme `X_k̄` is supported on the empty scheme-theoretic closure. -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_isEmpty
    (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n)))) [IsEmpty X.1] (i : ℤ) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  by_cases hi0 : i < 0
  · exact LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg
      B X ℓ f j kbar F i hi0
  refine LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_perfect_of_reduction
    B X ℓ f j kbar p q hcard F hP (-1) (fun n i' hi' ↦ ?_) i (by omega)
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, i' = q' := ⟨i'.toNat, by omega⟩
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (ZMod ℓ) _ _ q' ?_
  have : QuasiCompact (pullback.snd f (specAlgebraMap k kbar)) := inferInstance
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) := by
    rw [compactificationFieldBaseChange_immersion_comp_snd]
    infer_instance
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar) :=
    QuasiCompact.of_comp _ (pullback.snd j.toBase (specAlgebraMap k kbar))
  have : IsEmpty ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    ⟨fun z ↦ isEmptyElim (pullback.fst f (specAlgebraMap k kbar) z)⟩
  exact subsingleton_sheafH_of_isZero_etaleRestriction_of_isEmpty
    (compactificationFieldBaseChangeImmersion f j kbar) _
    (fun v _ hv ↦ isZero_etaleRestriction_coextendScalars_fieldBaseChange_extensionByZero f j kbar
      _ _ v hv) q'

omit [IsSeparated f] [CharP kbar p] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is nonzero for `0 ≤ i ≤ 2 dim X` only**, the degree bound of
[Stacks, Tag 03V2], given the perfectness of the complexes `RΓ_c(X_k̄, F'ₙ)` of the torsion-free
model and the absolute case of [Stacks, Tag 095U] over `k̄`. When `Hⁱ_c` is nonzero, `X` is
nonempty, so its dimension is a natural number `d` (it is at most that of the proper
compactification), and `0 ≤ i ≤ 2d`. -/
theorem LAdicSheaf.nontrivial_rationalGeometricCompactlySupportedCohomology_bounds
    (h095U : ProperSeparablyClosedSheafHVanishingStatement.{u}) (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n)))) (i : ℤ)
    (hi : Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)) :
    0 ≤ i ∧ ∃ d : ℕ, topologicalKrullDim X.1 = d ∧ i ≤ 2 * (d : ℤ) := by
  have hnz : ∀ M : ModuleCat.{u + 1} ℚ_[ℓ], Nontrivial M → ¬ IsZero M := fun M hM h ↦
    (not_subsingleton_iff_nontrivial.2 hM) (ModuleCat.subsingleton_of_isZero h)
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hnz _ hi (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg
      B X ℓ f j kbar F i (by omega))
  · by_cases hX : IsEmpty X.1
    · exact (hnz _ hi (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_isEmpty
        B X ℓ f j kbar p q hcard F hP i)).elim
    · rw [not_isEmpty_iff] at hX
      have : IsProper j.toBase := j.property.2
      have hne : Nonempty (j.obj.right.left : Scheme.{u}) := ⟨j.immersion hX.some⟩
      obtain ⟨d', hd'⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper k j.toBase hne
      have hle : topologicalKrullDim X.1 ≤ d' :=
        hd' ▸ j.immersion.isOpenEmbedding.isInducing.topologicalKrullDim_le
      have hbot : topologicalKrullDim X.1 ≠ ⊥ := by
        rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
        exact fun h ↦ h.false hX.some
      obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
      have hmtop : m ≠ ⊤ := by
        rintro rfl
        rw [← hm] at hle
        exact absurd (WithBot.coe_le_coe.mp hle) (by simp)
      refine ⟨m.toNat, by rw [← hm]; exact congrArg _ (ENat.natCast_toNat hmtop).symm, ?_⟩
      by_contra h
      exact hnz _ hi
        (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le
          B X ℓ f j kbar p q hcard h095U F hP m.toNat
          (by rw [← hm]; exact (congrArg _ (ENat.natCast_toNat hmtop).symm).le) i (by omega))

end Stacks.EtaleCohomology

end

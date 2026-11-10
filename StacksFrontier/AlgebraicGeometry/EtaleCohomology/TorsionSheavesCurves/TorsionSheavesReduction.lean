module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsExtUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFilteredColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TorsionConstructibleSubsheaves

/-!
# The reduction theorem for Theorem 03SC

In Situation 0A52 statements (1) -- (8) hold for every torsion abelian sheaf, granted Lemma 0A5B
for `Z/ℓ` on smooth curves for every prime `ℓ`. This is the proof of Theorem 03SC of the source
with its base case as the one hypothesis, at the coefficients `AddCommGrpCat.{u + 1}` and
with `Ext` in the universe `u + 1`.

## Main results

* `Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty`: **the reduction theorem.**
* `Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_of_hasExt`: the same with `Ext`
  in an arbitrary universe.

## Implementation notes

The constructible case is `Stacks.EtaleCohomology.curveStatements_of_isConstructible`. A torsion
sheaf `F` is the filtered colimit of constructible subsheaves
(`Stacks.EtaleCohomology.exists_isColimit_isConstructibleOnEveryBigSite_mono`, Tag 03SA (2)),
each of which inherits the torsion conditions of statements (3) and (6); statements (1), (2),
(3), (6), (7), (8) pass to the colimit because étale cohomology and the restriction maps commute
with filtered colimits on quasi-compact quasi-separated schemes (Tag 03Q5, module
`CurveStatementsFilteredColimit` of `StacksFrontier.AlgebraicGeometry.EtaleCohomology`, in
`TorsionSheavesCurves`), and statements (4) and (5) assume `F` constructible, so they are the
constructible case.

**No `@[stacks 03SC]` attribute**: Lemma 0A5B for `Z/ℓ` enters as a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- **The reduction theorem for Theorem 03SC.** Let `X` be a separated scheme of finite type and
dimension at most one over an algebraically closed field `k` and `F` a torsion abelian sheaf on
`X_étale`. If statements (1) -- (8) hold for `Z/ℓ` on every smooth curve over `k`, for every
prime `ℓ`, then statements (1) -- (8) of Situation 0A52 hold for `F`. -/
theorem curveStatements_of_torsionSheafProperty {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    CurveStatements.{u, 0, u + 1} π F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsNoetherian X := ⟨⟩
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ := exists_isColimit_isConstructibleOnEveryBigSite_mono F hF
  have hDj : ∀ j, CurveStatements.{u, 0, u + 1} π (D.obj j) := fun j ↦
    curveStatements_of_isConstructible π hdim hbase _ (hD j).1
  have hcF : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X),
      IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F → CurveStatements.{u, 0, u + 1} π F :=
    fun B hX h ↦ curveStatements_of_isConstructible π hdim hbase F
      (IsConstructibleOnEveryBigSite.of_contains hX h)
  have hscalar : ∀ (k' : Type u) [Field k'] [Algebra k k'],
      CompactSpace (scalarExtension k k' π) ∧ QuasiSeparatedSpace (scalarExtension k k' π) :=
    fun k' _ _ ↦ ⟨QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k')))),
      quasiSeparatedSpace_of_quasiSeparated
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))⟩
  refine
    { vanishing := fun q hq ↦ subsingleton_sheafH_of_isColimit hc q
        (fun j ↦ (hDj j).vanishing q hq)
      affineVanishing := fun hX q hq ↦ subsingleton_sheafH_of_isColimit hc q
        (fun j ↦ (hDj j).affineVanishing hX q hq)
      primePowerVanishing := fun p _ hp htors q hq ↦ subsingleton_sheafH_of_isColimit hc q
        (fun j ↦ (hDj j).primePowerVanishing p hp
          (have := (hD j).2; isPrimePowerTorsion_of_mono (ι.app j) htors) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun B hX _ _ h ↦
        (hcF B hX h).finite_of_isPrimeToCharacteristicTorsion B hX h
      finite_of_isProper := fun B hX _ _ hπ h ↦ (hcF B hX h).finite_of_isProper B hX hπ h
      bijective_of_isPrimeToCharacteristicTorsion := fun htors k' _ _ _ _ _ q ↦ ?_
      bijective_of_isProper := fun hπ k' _ _ _ _ _ q ↦ ?_
      surjective := fun U _ ↦ ?_ }
  · obtain ⟨_, _⟩ := hscalar k'
    exact bijective_etaleCohomologyRestrictionMap_of_isColimit hc (scalarExtensionFst k k' π) q
      (fun j ↦ (hDj j).bijective_of_isPrimeToCharacteristicTorsion
        (have := (hD j).2; isPrimeToCharacteristicTorsion_of_mono (ι.app j) htors) k' q)
  · obtain ⟨_, _⟩ := hscalar k'
    exact bijective_etaleCohomologyRestrictionMap_of_isColimit hc (scalarExtensionFst k k' π) q
      (fun j ↦ (hDj j).bijective_of_isProper hπ k' q)
  · have : CompactSpace U := isCompact_iff_compactSpace.1
      (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
    have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated U.ι
    exact surjective_etaleCohomologyRestrictionMap_of_isColimit hc U.ι 2
      (fun j ↦ (hDj j).surjective U)

/-- **The reduction theorem for Theorem 03SC, `Ext` in any universe.** The statement of
`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty` with étale cohomology computed by
`Ext` in an arbitrary universe `w`. -/
theorem curveStatements_of_torsionSheafProperty_of_hasExt {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    CurveStatements.{u, 0, w} π F :=
  CurveStatements.ofSucc (curveStatements_of_torsionSheafProperty π hdim hbase F hF)

end Stacks.EtaleCohomology

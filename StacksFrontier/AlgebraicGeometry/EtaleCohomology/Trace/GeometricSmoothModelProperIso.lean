module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCoverConstantCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry

/-!
# The smooth projective model of a proper geometric curve is the curve itself

Let `X` be a geometrically connected smooth curve over `k`, `X̄` a compactification and `C` the
smooth projective model of `X_k̄` (`Stacks.EtaleCohomology.geometricSmoothModel`), with its open
immersion `j : X_k̄ ⟶ C`. If `X_k̄` is proper over `k̄` then `j` is an isomorphism: `j` is proper
because `C` is separated, so its image is open and closed, hence everything since `C` is
connected. Consequently `H^i(C, j_! G) ≅ H^i(X_k̄, G)` for every sheaf `G`: compactly supported
cohomology of a proper curve is its cohomology.

## Main results

* `Stacks.EtaleCohomology.geometricSmoothModel_j_comp_q` — `j` followed by the structure
  morphism of `C` is the structure morphism of `X_k̄`.
* `Stacks.EtaleCohomology.isIso_geometricSmoothModel_j` — `j` is an isomorphism when `X_k̄` is
  proper.
* `Stacks.EtaleCohomology.geometricSmoothModelProperExtensionByZeroIso`,
  `Stacks.EtaleCohomology.geometricSmoothModelProperRightDerivedPlusIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesSmoothModelProper (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y) :=
  Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, 0} Λ Y

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]

omit [Algebra.IsAlgebraic k kbar] in
/-- `j : X_k̄ ⟶ C` followed by the structure morphism of `C` is the structure morphism of
`X_k̄`. -/
lemma geometricSmoothModel_j_comp_q :
    (geometricSmoothModel f j kbar).j ≫ (geometricSmoothModel f j kbar).q =
      pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar) := by
  rw [(geometricSmoothModel f j kbar).j_comp_q (pullback.snd f (Stacks.Frobenius.specAlgebraMap k
    kbar)) (compactificationFieldBaseChange_immersion_comp_snd f j kbar), Category.id_comp]

omit [Algebra.IsAlgebraic k kbar] in
/-- **The smooth projective model of a proper `X_k̄` is `X_k̄`**: the open immersion
`j : X_k̄ ⟶ C` is an isomorphism. -/
theorem isIso_geometricSmoothModel_j
    (hp : IsProper (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar))) :
    IsIso (geometricSmoothModel f j kbar).j := by
  have : UniversallyClosed
      ((geometricSmoothModel f j kbar).j ≫ (geometricSmoothModel f j kbar).q) := by
    rw [geometricSmoothModel_j_comp_q]
    infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (geometricSmoothModel f j kbar).j
    (geometricSmoothModel f j kbar).q
  have : ConnectedSpace (pullback f (Stacks.Frobenius.specAlgebraMap k kbar) : Scheme.{u}) :=
    AlgebraicGeometry.connectedSpace_fieldBaseChange f kbar
  have : Nonempty (pullback f (Stacks.Frobenius.specAlgebraMap k kbar) : Scheme.{u}) :=
    ConnectedSpace.toNonempty
  rw [isIso_iff_isOpenImmersion_and_surjective]
  have hclopen : IsClopen (Set.range (geometricSmoothModel f j kbar).j.base) :=
    ⟨(geometricSmoothModel f j kbar).j.isClosedMap.isClosed_range,
      (geometricSmoothModel f j kbar).j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range (geometricSmoothModel f j kbar).j.base).Nonempty :=
    Set.range_nonempty _
  exact ⟨inferInstance, ⟨Set.range_eq_univ.mp (hclopen.eq_univ hne)⟩⟩

variable (Λ : Type) [Ring Λ]
  (hp : IsProper (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar)))

/-- **`j_! G ≅ j_* G`** along the isomorphism `j : X_k̄ ⟶ C` of a proper `X_k̄`. -/
def geometricSmoothModelProperExtensionByZeroIso
    (G : EtaleModules.{u, 0} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))) :
    (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj G ≅
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj G :=
  haveI := isIso_geometricSmoothModel_j f j kbar hp
  haveI : IsIntegralHom (geometricSmoothModel f j kbar).j :=
    inferInstance
  (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).mapIso
      ((etaleModuleDirectImageIdIso Λ _).app G).symm ≪≫
    (extensionByZeroDirectImageIntegralIso Λ (geometricSmoothModel f j kbar).j (𝟙 _) (𝟙 _)
      (geometricSmoothModel f j kbar).j (IsKernelPair.id_of_mono _)).app G ≪≫
    (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).j).mapIso
      ((etaleModuleExtensionByZeroIdIso Λ _).app G)

/-- **`H^i(C, j_! G) ≅ H^i(X_k̄, G)`** for a proper `X_k̄`. -/
def geometricSmoothModelProperRightDerivedPlusIso
    (G : EtaleModules.{u, 0} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))) (i : ℤ) :
    letI := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus i).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj G) ≅
      letI := HasDerivedCategory.standard
        (EtaleModules.{u, 0} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar)))
      letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
      ((etaleModuleGlobalSections.{u, 0} Λ
        (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))).rightDerivedPlus i).obj G :=
  letI := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  letI := HasDerivedCategory.standard
    (EtaleModules.{u, 0} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar)))
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  haveI := isIso_geometricSmoothModel_j f j kbar hp
  haveI : IsIntegralHom (geometricSmoothModel f j kbar).j :=
    inferInstance
  ((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedPlus i).mapIso
      (geometricSmoothModelProperExtensionByZeroIso f j kbar Λ hp G) ≪≫
    integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).j G i

end Stacks.EtaleCohomology

end

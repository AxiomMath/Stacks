module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyWithSupportTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HigherDirectImageModels

/-!
# The spectral sequence of the sections with support in a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. Stacks 0A4L
deduces from Stacks 0A4M a Grothendieck spectral sequence

`E_2^{p,q} = H^p(Z, 𝓗^q_Z(F)) ⇒ H^{p+q}_Z(X, F)`

for an abelian sheaf `F` on `X_étale`. This file proves it.

## Main definitions

* `AlgebraicGeometry.Space.closedImmersionPushforwardGlobalSectionsIso`: global sections over
  `X` of a direct image along `i` are the global sections over `Z`, `Γ(X, i_* G) = Γ(Z, G)`.
* `AlgebraicGeometry.Space.closedGlobalSectionsWithSupportIsoComp`: the sections with support
  factor as `Γ_Z(X, -) = Γ(Z, -) ∘ 𝓗_Z`.

## Main results

* `AlgebraicGeometry.Space.exists_abutsTo_sectionsWithSupportSpectralSequence`: the spectral
  sequence.

## Implementation notes

Both identifications are read on the spaces-étale sites of Stacks 03G0, where global sections
are the sections at the terminal object: the direct image along `i` there is restriction along
base change of étale algebraic spaces, which carries the terminal object `X` to `X ×_X Z`, a
terminal object of the spaces-étale site of `Z`. The factorization of `Γ_Z(X, -)` is then the
identification `H_Z(F) = i_* 𝓗_Z(F)` of the subsheaf of sections supported on `|Z|`. The
spectral sequence is the Grothendieck spectral sequence of the composite `Γ(Z, -) ∘ 𝓗_Z`, whose
acyclicity hypothesis is Stacks 0A4M: `𝓗_Z` carries injective sheaves to injective sheaves.

The degrees are the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`; the comparison with
the `ℕ`-indexed `CategoryTheory.Functor.rightDerived` in which
`AlgebraicGeometry.Space.closedCohomologyWithSupport` is defined is
`Stacks.DerivedIndexing.rightDerivedIso`.

## References

* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **Global sections of a direct image along a closed immersion.**  For an abelian sheaf `G`
on `Z_étale`, the global sections over `X` of `i_* G` are the global sections of `G`, naturally
in `G`.  On the spaces-étale sites, `i_*` is restriction along base change of étale algebraic
spaces, and the base change of the terminal object `X` is a terminal object of the
spaces-étale site of `Z`. -/
def closedImmersionPushforwardGlobalSectionsIso :
    smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
  letI := isContinuous_smallBaseChange B S hS i hi.rep
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (spacesEtaleChartRestriction B S hS Z
        (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso.symm
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (spacesEtaleChartRestriction B S hS Z (A := AddCommGrpCat.{u + 1})).inv
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallBaseChangePushforwardComparison B S hS i hi.rep
          AddCommGrpCat.{u + 1}) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (ΓTerminalNatIso B S hS X).symm ≪≫
        (sheafSections (SpacesEtale.topology B S hS Z) AddCommGrpCat.{u + 1}).mapIso
          ((isTerminal_spacesBaseChange_idObj B S hS i).uniqueUpToIso
            (SpacesEtale.isTerminal_idObj B S hS Z)).op.symm ≪≫
        ΓTerminalNatIso B S hS Z) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (spacesEtaleChartRestriction B S hS Z (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso
      _ ≪≫
    Functor.leftUnitor _

/-- **The sections with support factor through `𝓗_Z`**: `Γ_Z(X, F) = Γ(Z, 𝓗_Z(F))`, naturally in
the abelian sheaf `F` on `X_étale`. -/
def closedGlobalSectionsWithSupportIsoComp :
    closedGlobalSectionsWithSupport B S hS i ≅
      sectionsWithSupportInClosedSubspace B S hS i hi ⋙
        Sheaf.Γ (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight (closedSectionsWithSupportIsoPushforward B S hS i hi)
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (closedImmersionPushforwardGlobalSectionsIso B S hS i hi)

section SpectralSequence

-- Raising the priority of this instance lets the bounded below right derived functor of global
-- sections be found; at the default priority the search times out.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The spectral sequence of Stacks 0A4L.**  Let `i : Z ⟶ X` be a closed immersion of
algebraic spaces over `S` and let `F` be an abelian sheaf on `X_étale`.  There is a
cohomological spectral sequence with second page

`E_2^{p,q} ≅ H^p(Z, 𝓗^q_Z(F))`

abutting to the cohomology with support `n ↦ H^n_Z(X, F)`: some finite decreasing filtration of
each `H^n_Z(X, F)` has the terms `E_∞^{p, n-p}` as its graded pieces.

Here `H^p(Z, -)` is the `p`-th right derived functor of global sections on `Z_étale`, `𝓗^q_Z` is
`AlgebraicGeometry.Space.higherSectionsWithSupportInClosedSubspace`, the `q`-th right derived
functor of `𝓗_Z`, and `H^n_Z(X, -)` is the `n`-th right derived functor of `Γ_Z(X, -)`, all in the
`ℤ`-indexed convention `CategoryTheory.Functor.rightDerivedPlus`.

It is the Grothendieck spectral sequence of the composite `Γ(Z, -) ∘ 𝓗_Z = Γ_Z(X, -)`
(`AlgebraicGeometry.Space.closedGlobalSectionsWithSupportIsoComp`), whose acyclicity hypothesis
is Stacks 0A4M: `𝓗_Z` sends injective abelian sheaves on `X_étale` to injective abelian sheaves
on `Z_étale`, which are acyclic for `Γ(Z, -)`. -/
@[stacks 0A4L "the spectral sequence E_2^{p,q} = H^p(Z, 𝓗^q_Z(F)) ⇒ H^{p+q}_Z(X, F)"]
theorem exists_abutsTo_sectionsWithSupportSpectralSequence
    [HasDerivedCategory (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((Sheaf.Γ (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1}).rightDerivedPlus p).obj
          ((higherSectionsWithSupportInClosedSubspace B S hS i hi q).obj F))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        ((closedGlobalSectionsWithSupport B S hS i).rightDerivedPlus n).obj F) := by
  obtain ⟨K, hrest⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
    (sectionsWithSupportInClosedSubspace B S hS i hi)
    (Sheaf.Γ (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (fun I hI => by
      have := hI
      have := injective_sectionsWithSupportInClosedSubspace_of_isClosedImmersion B S hS i hi I
      exact Functor.rightAcyclic_of_injective _ _)
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) 0).obj F)
  obtain ⟨E, -, hE₂, habuts⟩ :=
    hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  refine ⟨E, fun p q => ?_, habuts.of_iso fun n => ?_⟩
  · obtain ⟨e⟩ := hE₂ p q
    exact ⟨e ≪≫
      ((Sheaf.Γ (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1}).rightDerivedPlus p).mapIso
        (StacksDraft.DerivedModel.PlusTransport.rightDerivedPlusModelIso inferInstance
          (HasDerivedCategory.standard _) inferInstance (HasDerivedCategory.standard _)
          (sectionsWithSupportInClosedSubspace B S hS i hi) q F)⟩
  exact (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso
    (closedGlobalSectionsWithSupportIsoComp B S hS i hi) n).symm.app F

end SpectralSequence

end AlgebraicGeometry.Space

end

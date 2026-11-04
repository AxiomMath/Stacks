module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.Finiteness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic

/-!
# Top-degree coherent cohomology of an open subscheme of a proper scheme

Let `Y` be proper over a field `k` of dimension at most `d` and `j : X ⟶ Y` an open immersion.
For a coherent `𝒪_X`-module `F`, `H^d(X, F)` is finite-dimensional: `F` extends to a coherent
module `G` on `Y` ([Stacks, Tag 0G41]), `H^d(Y, G)` is finite-dimensional ([Stacks, Tag 02O6]) and
restriction `H^d(Y, G) ⟶ H^d(X, F)` is onto ([Stacks, Tag 0A3G] clause (2)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.CohomologyScalars

/-- **Top-degree coherent cohomology of an open subscheme of a proper scheme over a field is
finite-dimensional.** -/
theorem finiteDimensional_top_of_isOpenImmersion_of_isProper (k : Type u) [Field k]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (g : Y ⟶ Spec (.of k)) [IsProper g]
    (d : ℕ) (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsCoherent) :
    FiniteDimensional k (cohomologyOverField k (j ≫ g) F d) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Y := { }
  let U := j.opensRange
  let e := j.isoOpensRange
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (j ≫ g)
  let Fopen : U.toScheme.Modules := (Scheme.Modules.restrictFunctor e.inv).obj F
  have hFopen : Fopen.IsCoherent := isCoherent_restrict_of_isOpenImmersion e.inv F hF
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent Fopen
  obtain ⟨G, hGqc, hGft, ⟨eG⟩⟩ :=
    exists_extension_of_isQuasicoherent_isFiniteType U (NoetherianSpace.isCompact _) Fopen
  have : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType G
  have : FiniteDimensional k (cohomologyOverField k g G d) :=
    finiteDimensional_cohomologyOverField_of_isProper k g G d
  have hres := finiteDimensional_cohomologyOverField_restrict' k j g d hdim G
  let iso : (Scheme.Modules.restrictFunctor j).obj G ≅ F :=
    (restrictFunctorIsoRange j).symm.app G ≪≫
      (Scheme.Modules.restrictFunctor e.hom).mapIso eG ≪≫
      ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app F ≪≫
      Scheme.Modules.restrictFunctorId.app F
  exact (cohomologyOverFieldIso k (j ≫ g) iso d).toLinearEquiv.finiteDimensional

end AlgebraicGeometry.CohomologyScalars

end

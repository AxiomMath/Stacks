module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretationDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTrivializedStratification

/-!
# Reduction of [Stacks, Tag 03UZ] to Galois-trivialized lisse strata

Let `X` be a separated scheme of finite type over a finite field and `F` a constructible flat sheaf
of `Λ`-modules. By
`AlgebraicGeometry.exists_galoisTrivialized_stageStratification_of_isConstructibleFlatModuleSheaf`
the open strata of a closed filtration of `X` are smooth and irreducible, and on each of them `F`
is the descent sheaf of a finite projective `Λ`-module along a connected finite étale Galois
covering. If on every such stratum, for every compactification,
`det(1 - π^* T | RΓ_c) · L = 1`, then the identity of Tag 03UZ holds on `X` for every
compactification (`Stacks.EtaleCohomology.compactSupportCharSeriesInverts_lFunction_of_stages`).

## Main results

* `Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_lisse`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [CommRing Λ] [Finite Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identity of Tag 03UZ from its lisse case.** If the identity
`det(1 - π^* T | RΓ_c) · L = 1` holds, for every compactification, on every smooth irreducible
`Z ⟶ X` along which `F` is the descent sheaf of a finite projective module along a connected
finite étale Galois covering, then it holds on `X` for every compactification. -/
theorem lFunctionCharSeriesIdentity_of_lisse (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (hlisse : ∀ (Z : B.Scheme) (g : Z ⟶ X) [LocallyOfFiniteType (B.inclusion.map g ≫ f)]
      [QuasiCompact (B.inclusion.map g ≫ f)] [IsSeparated (B.inclusion.map g ≫ f)]
      (H : Type) [Group H] [Fintype H] (C : EtaleGaloisCovering Z.obj H) (N : Type (u + 1))
      [AddCommGroup N] [Module Λ N] (ρ : H →* Module.End Λ N),
      Module.Finite Λ N → Module.Projective Λ N → IsFinite C.cover.hom →
      ConnectedSpace C.cover.left → IrreducibleSpace Z.obj → Smooth (B.inclusion.map g ≫ f) →
      ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj
        (smallEtalePullObj B g F) ≅ C.descentSheaf.{u, 0, 0, 0} Λ N ρ) →
      ∀ (hfin : ∀ s : GeometricPoint Z.obj, Module.Finite Λ
          ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj (smallEtalePullObj B g F)))
        (hproj : ∀ s : GeometricPoint Z.obj, Module.Projective Λ
          ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj (smallEtalePullObj B g F)))
        (J : CompactificationOf (Over.mk (B.inclusion.map g ≫ f))),
        CompactSupportCharSeriesInverts Λ kbar p q hcard _ J
          ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj
            (smallEtalePullObj B g F))
          (lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B Z Λ (smallEtalePullObj B g F)
            (B.inclusion.map g ≫ f) hfin hproj))
    (J : CompactificationOf (Over.mk f)) :
    LFunctionCharSeriesIdentity B X Λ f kbar F hF J p q hcard := by
  obtain ⟨s, Φ, hdata⟩ :=
    exists_galoisTrivialized_stageStratification_of_isConstructibleFlatModuleSheaf B X Λ f hF
  refine lFunctionCharSeriesIdentity_of_compactSupportCharSeriesInverts B X Λ F f kbar p q
    hcard hF J ?_
  refine compactSupportCharSeriesInverts_lFunction_of_stages B X Λ F _ _ f Φ kbar p q hcard
    (fun i J' => ?_) J
  obtain ⟨hirr, hsm, -, H, _, _, C, N, _, _, ρ, hNf, hNp, hfinC, hconn, ⟨e⟩⟩ := hdata i
  have : TopologicalSpace.NoetherianSpace (B.inclusion.obj (Φ.stageOpenObj i)) :=
    noetherianSpace_stratum B X f Φ.toStageStratification i
  have : IsImmersion (B.inclusion.map (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i)) :=
    Φ.toStageStratification.isImmersion i
  exact hlisse (Φ.stageOpenObj i) (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) H C N ρ hNf hNp
    hfinC hconn hirr hsm e _ _ J'

end Stacks.EtaleCohomology

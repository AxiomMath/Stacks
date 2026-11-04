module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToBigEtaleDerivedUnitIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleChartDerivedPullback

/-!
# Good modules from complexes of quasi-coherent modules

Let `Y` be an algebraic space and `C` a complex of quasi-coherent `𝒪_Y`-modules on the
spaces-étale site of `Y`. The cohomology sheaves of `π_Y^*C` on the big étale site of `Y` are, by
Stacks 0DGQ, of the form `ε_{Y,*}𝓗` with `𝓗` an fppf module without higher cohomology on affine
objects; in particular the unit `𝓖 ⟶ ε_{Y,*}ε_Y^*𝓖` is invertible at them, since `ε_{Y,*}` is fully
faithful, and they and their fppf sheafifications have no higher cohomology on affine objects.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.LocallyGood`: the unit `𝓖 ⟶ ε_{Y,*}ε_Y^*𝓖` is invertible and
  `𝓖`, `ε_Y^*𝓖` have no higher cohomology on affine objects.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_pushforwardTopos_full`,
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_pushforwardTopos_faithful`: the pushforward
  `ε_{X,*}` from fppf to big étale modules is fully faithful.
* `AlgebraicGeometry.BigFppfSpaceSite.good_homology_of_iso_pullback_quasicoherent`: the cohomology
  sheaves of `π_Y^*C`, for a complex `C` of quasi-coherent modules, are `LocallyGood`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **`ε_{X,*}` is full**: after identifying the two sites it is the inclusion of fppf sheaves among
étale sheaves. -/
instance fppfToBigEtale_pushforwardTopos_full (X : T.Spaces) :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.Full := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      have htop : E'.topology ≤ T'.topology := by
        change E'.precoverage.toGrothendieck ≤ T'.precoverage.toGrothendieck
        intro U R hR
        rw [Precoverage.mem_toGrothendieck_iff] at hR ⊢
        induction hR with
        | of U R hR =>
            rw [BigEtaleSpaceSite.mem_precoverage_iff] at hR
            rcases hR with ⟨E₀, rfl, hE₀⟩
            obtain ⟨E₁, hE₁, hU, hCE⟩ := tRepresentative ⟨U, E₀⟩
              (Space.isFppfCovering_of_isEtaleCovering tScheme S eFppfMem
                (BigEtaleSpaceSite.IsCovering.etale hE₀))
            change U = E₁.1 at hU
            subst hU
            rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE]
            refine Precoverage.generate_mem_toGrothendieck ?_
            rw [BigFppfSpaceSite.mem_precoverage_iff]
            exact ⟨E₁.2, rfl, hE₁⟩
        | top => exact T'.topology.top_mem _
        | pullback U R _ V f ih => exact T'.topology.pullback_stable _ ih
        | transitive U R R' _ _ ihR ihT => exact T'.topology.transitive ihR _ fun V g hg ↦ ihT hg
      have hle : E'.topology.over X ≤ T'.topology.over X := fun Z R hR => by
        rw [GrothendieckTopology.mem_over_iff] at hR ⊢
        exact htop Z.left hR
      exact @Functor.Full.of_iso _ _ _ _ _ _ (SheafOfModules.fullyFaithfulOfLE hle
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T' X).O)).full
        ((bigFppfRingedSite T' X).pushforwardToposCoarseningHomIso hle).symm

/-- `ε_{X,*}` is faithful. -/
instance fppfToBigEtale_pushforwardTopos_faithful (X : T.Spaces) :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.Faithful := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      have htop : E'.topology ≤ T'.topology := by
        change E'.precoverage.toGrothendieck ≤ T'.precoverage.toGrothendieck
        intro U R hR
        rw [Precoverage.mem_toGrothendieck_iff] at hR ⊢
        induction hR with
        | of U R hR =>
            rw [BigEtaleSpaceSite.mem_precoverage_iff] at hR
            rcases hR with ⟨E₀, rfl, hE₀⟩
            obtain ⟨E₁, hE₁, hU, hCE⟩ := tRepresentative ⟨U, E₀⟩
              (Space.isFppfCovering_of_isEtaleCovering tScheme S eFppfMem
                (BigEtaleSpaceSite.IsCovering.etale hE₀))
            change U = E₁.1 at hU
            subst hU
            rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE]
            refine Precoverage.generate_mem_toGrothendieck ?_
            rw [BigFppfSpaceSite.mem_precoverage_iff]
            exact ⟨E₁.2, rfl, hE₁⟩
        | top => exact T'.topology.top_mem _
        | pullback U R _ V f ih => exact T'.topology.pullback_stable _ ih
        | transitive U R R' _ _ ihR ihT => exact T'.topology.transitive ihR _ fun V g hg ↦ ihT hg
      have hle : E'.topology.over X ≤ T'.topology.over X := fun Z R hR => by
        rw [GrothendieckTopology.mem_over_iff] at hR ⊢
        exact htop Z.left hR
      exact @Functor.Faithful.of_iso _ _ _ _ _ _ (SheafOfModules.fullyFaithfulOfLE hle
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T' X).O)).faithful
        ((bigFppfRingedSite T' X).pushforwardToposCoarseningHomIso hle).symm

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasExt_bigFppfSpaceOver BigEtaleSpaceSite.hasExt_bigEtaleSpaceOver

/-- Vanishing of `H' · p U` transfers backwards along an isomorphism of abelian sheaves. -/
private theorem isZero_H'_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{_}] [HasExt.{_} (Sheaf J AddCommGrpCat.{_})]
    {F F' : Sheaf J AddCommGrpCat.{_}} (e : F ≅ F') {p : ℕ} {U : C}
    (h : IsZero (Sheaf.H' F' p U)) : IsZero (Sheaf.H' F p U) :=
  h.of_iso (((Sheaf.cohomologyPresheafFunctor _ p).mapIso e).app (Opposite.op U))

/-- **Good modules on the big étale site of `Y`, tested on all affine objects**: the unit
`𝓖 ⟶ ε_{Y,*}ε_Y^*𝓖` is invertible, and `𝓖`, resp. `ε_Y^*𝓖`, has no higher cohomology on the
affine objects of `(Spaces/Y)_étale`, resp. `(Spaces/Y)_fppf`. -/
abbrev LocallyGood (Y : T.Spaces)
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)) :
    Prop :=
  IsIso ((epsilonHom T E h Y).pullbackPushforwardAdjunctionTopos.unit.app G) ∧
    (∀ U : Over (etaleSpace T E h Y),
      BigEtaleSpaceSite.IsAffineSchemeOver E (etaleSpace T E h Y) U → ∀ p : ℕ, 0 < p →
        IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj G) p U)) ∧
    (∀ U : Over Y, BigFppfSpaceOver.IsAffineSchemeOver T Y U → ∀ p : ℕ, 0 < p →
        IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj ((epsilonHom T E h Y).pullbackTopos.obj G))
          p U))

/-- `LocallyGood` is invariant under isomorphism of modules. -/
theorem LocallyGood.of_iso {Y : T.Spaces}
    {G G' : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)}
    (e : G ≅ G') (hG : LocallyGood T E h Y G) : LocallyGood T E h Y G' := by
  obtain ⟨h₁, h₂, h₃⟩ := hG
  exact ⟨(NatTrans.isIso_app_iff_of_iso _ e).1 h₁,
    fun U hU p hp ↦ isZero_H'_of_iso ((SheafOfModules.toSheaf _).mapIso e.symm) (h₂ U hU p hp),
    fun U hU p hp ↦ isZero_H'_of_iso ((SheafOfModules.toSheaf _).mapIso
      ((epsilonHom T E h Y).pullbackTopos.mapIso e.symm)) (h₃ U hU p hp)⟩

/-- **The cohomology sheaves of `π_Y^*C` are good, for a complex `C` of quasi-coherent modules
(Stacks 0DGQ).** If `L ≅ π_Y^*C` in `D((Spaces/Y)_étale)`, then every `𝓖 = H^q(L)` has invertible
unit `𝓖 ⟶ ε_{Y,*}ε_Y^*𝓖`, and `𝓖` and `ε_Y^*𝓖` have no higher cohomology on affine objects. -/
theorem good_homology_of_iso_pullback_quasicoherent (Y : T.Spaces)
    (C : CochainComplex (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h Y)).O)) ℤ)
    (hqc : ∀ n, (C.X n).IsQuasicoherentOnSite)
    (L : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)))
    (e : L ≅ DerivedCategory.Q.obj
      (((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h Y)).toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))
    (q : ℤ) :
    LocallyGood T E h Y ((DerivedCategory.homologyFunctor _ q).obj L) := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let C' : CochainComplex (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem Y).O)) ℤ := C
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    have : (C'.sc q).X₁.IsQuasicoherentOnSite := hqc _
    have : (C'.sc q).X₂.IsQuasicoherentOnSite := hqc _
    have : (C'.sc q).X₃.IsQuasicoherentOnSite := hqc _
    obtain ⟨⟨eH⟩, het, hfppf⟩ := homology_pullback_of_quasicoherent T E' rfl Y (C'.sc q)
    let eG : (DerivedCategory.homologyFunctor _ q).obj L ≅ _ :=
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app _
    let adj := (epsilonHom T E' rfl Y).pullbackPushforwardAdjunctionTopos
    have : (epsilonHom T E' rfl Y).pushforwardTopos.Full :=
      fppfToBigEtale_pushforwardTopos_full T E' rfl Y
    have : (epsilonHom T E' rfl Y).pushforwardTopos.Faithful :=
      fppfToBigEtale_pushforwardTopos_faithful T E' rfl Y
    have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
    let eM := eG ≪≫ eH
    refine ⟨(Adjunction.isIso_unit_app_iff_mem_essImage adj).mpr ⟨_, ⟨eM.symm⟩⟩,
      fun U hU p hp ↦ isZero_H'_of_iso ((SheafOfModules.toSheaf _).mapIso eG) (het U hU p hp),
      fun U hU p hp ↦ isZero_H'_of_iso ((SheafOfModules.toSheaf _).mapIso
        ((epsilonHom T E' rfl Y).pullbackTopos.mapIso eM ≪≫ (asIso adj.counit).app _))
        (hfppf U hU p hp)⟩

end AlgebraicGeometry.BigFppfSpaceSite

end

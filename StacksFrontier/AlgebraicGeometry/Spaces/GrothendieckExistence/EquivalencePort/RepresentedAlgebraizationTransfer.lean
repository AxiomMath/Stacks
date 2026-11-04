module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartAdicQuotientGeneric
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartBaseIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RepresentedChartSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit

namespace Stacks.Algebraization.HasProperSupport.C1573
end Stacks.Algebraization.HasProperSupport.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Algebraization on a represented algebraic space from algebraization on the scheme

Let `U` be an object of the big fppf site over `Spec A`, with scheme `T` locally of finite type
over `A`.  If every coherent `I`-adic system on `T` with support proper over `A` is the completion
of a coherent module with support proper over `A`, then the same holds on the algebraic space
`h_U`
(`AlgebraicGeometry.Space.C1573.exists_adicQuotientSystem_iso_of_scheme_algebraization`).  The
transfer is the Zariski restriction along the identity chart, which is fully faithful on
quasi-coherent modules, carries coherent adic systems to coherent adic systems and completions to
completions, and identifies the two notions of proper support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Stacks.Algebraization

open _root_.Stacks.Algebraization.C1573
/-- Proper support is invariant under isomorphism. -/
theorem HasProperSupport.C1573.of_iso {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType f] {F G : X.Modules} (e : F ≅ G)
    (h : HasProperSupport f F) : HasProperSupport f G := by
  obtain ⟨Z, hZ, hp⟩ := h
  exact ⟨Z, hZ.trans (SheafOfModules.supp_eq_of_iso e), hp⟩

/-- Proper support along equal morphisms. -/
theorem HasProperSupport.C1573.of_eq {X S : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ S}
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.LocallyOfFiniteType g]
    (h : f = g) {F : X.Modules} (hF : HasProperSupport f F) : HasProperSupport g F := by
  subst h
  exact hF

end Stacks.Algebraization

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- The structure morphism of a represented algebraic space to the base, read on schemes, is the
structure morphism of the representing object. -/
theorem C1573.toScheme_map_preimage_baseObject (U : BigFppfOver B (Spec (.of A)) hA)
    (f : yoneda.obj U ⟶ yoneda.obj (baseObject A B hA)) :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map (yoneda.preimage f) = B.inclusion.map U.hom := by
  show B.inclusion.map (yoneda.preimage f).left = _
  rw [← Over.w (yoneda.preimage f)]
  simp

/-- **Algebraization transfers from the scheme to the algebraic space it represents.** -/
theorem C1573.exists_adicQuotientSystem_iso_of_scheme_algebraization [IsNoetherianRing A]
    (I : Ideal A)
    (U : BigFppfOver B (Spec (.of A)) hA) [LocallyOfFiniteType (B.inclusion.map U.hom)]
    [IsLocallyNoetherian (B.inclusion.obj U.left)]
    (halg : ∀ E : Stacks.Coherent.CoherentAdicSystems
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (B.inclusion.map U.hom)),
      Stacks.Algebraization.HasProperSupport (B.inclusion.map U.hom) (E.obj.obj (op 0)) →
      ∃ F : AlgebraicGeometry.SheafOfModules.CoherentModules
          (B.inclusion.obj U.left).ringCatSheaf,
        Stacks.Algebraization.HasProperSupport (B.inclusion.map U.hom) F.obj ∧
          Nonempty ((Stacks.Algebraization.completionFunctor _
            (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (B.inclusion.map U.hom))).obj F ≅
              E))
    (f : schemeSpace U ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (G : CoherentAdicSystems B (Spec (.of A)) hA (yoneda.obj U)
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
      (baseIdealSubmodule (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) I))
    (hG0 : HasProperSupport B (Spec (.of A)) hA (schemeSpace U).2
      (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj (G.obj.obj (op 0)))) :
    ∃ F : Modules.{u, u} B (Spec (.of A)) hA (yoneda.obj U)
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U),
      IsCoherent B (Spec (.of A)) hA (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
          F ∧
        HasProperSupport B (Spec (.of A)) hA (schemeSpace U).2
          (schemeSpace (baseObject A B hA)).2 f.hom hf ((SheafOfModules.toSheaf _).obj F) ∧
        Nonempty (G.obj ≅ adicQuotientSystem B (Spec (.of A)) hA (yoneda.obj U)
          (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
          (baseIdealSubmodule (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) I)
          F) := by
  obtain ⟨fh⟩ := f
  obtain ⟨q, rfl⟩ : ∃ q : U ⟶ baseObject A B hA, yoneda.map q = fh :=
    ⟨yoneda.preimage fh, yoneda.map_preimage fh⟩
  have hq : (BigFppfOver.toScheme B (Spec (.of A)) hA).map q = B.inclusion.map U.hom :=
    toScheme_map_preimage_baseObject U (yoneda.map q) ▸ by rw [Functor.preimage_map]
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B (Spec (.of A)) hA).map q) :=
    hq ▸ inferInstance
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) :=
    inferInstanceAs (IsLocallyNoetherian (B.inclusion.obj U.left))
  have : IsLocallyNoetherian (chartScheme (idEtaleChart B (Spec (.of A)) hA U)) :=
    inferInstanceAs (IsLocallyNoetherian (B.inclusion.obj U.left))
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA (yoneda.obj U)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B (Spec (.of A)) hA _ _ U (Iso.refl _) inferInstance⟩
  have hK := map_chartSectionsRingHom_baseIdealSheaf
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩ I
    (idEtaleChart B (Spec (.of A)) hA U)
  have hIqc := isQuasicoherentOnSite_baseIdealSubmodule (X := yoneda.obj U)
    (hX := isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) I
  have hIcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA
    (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) _ hIqc
  let E : Stacks.Coherent.CoherentAdicSystems
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (B.inclusion.map U.hom)) :=
    ⟨G.obj ⋙ chartZariskiModule B (Spec (.of A)) hA
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩
      (idEtaleChart B (Spec (.of A)) hA U),
      isCoherentAdicSystem_chartZariskiModule B (Spec (.of A)) hA
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩)
        (idEtaleChart B (Spec (.of A)) hA U) _ _ hK hIcart G⟩
  have hE0 : Stacks.Algebraization.HasProperSupport (B.inclusion.map U.hom) (E.obj.obj (op 0)) :=
    Stacks.Algebraization.HasProperSupport.C1573.of_eq hq
      ((hasProperSupport_yoneda_map_iff B (Spec (.of A)) hA q hf (G.obj.obj (op 0))
        (G.property.1 0).toIsQuasicoherentOnSite).1 hG0)
  obtain ⟨FV, hFV, ⟨eV⟩⟩ := halg E hE0
  have : FV.obj.IsCoherent := FV.property
  have hFVq : FV.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent FV.obj
  let F := ((representedQuasicoherentSchemeEquivalence B (Spec (.of A)) hA U).functor.obj
    ⟨FV.obj, hFVq⟩).obj
  have hF : IsCoherent B (Spec (.of A)) hA (yoneda.obj U)
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) F :=
    isCoherent_representedQuasicoherentSchemeEquivalence B (Spec (.of A)) hA U FV.obj hFVq
      FV.property.isFiniteType
  obtain ⟨eΦ⟩ := nonempty_chartZariskiPushforward_idEtaleChart_iso B (Spec (.of A)) hA U FV.obj hFVq
  refine ⟨F, hF, ?_, ?_⟩
  · exact (hasProperSupport_yoneda_map_iff B (Spec (.of A)) hA q hf F
      hF.toIsQuasicoherentOnSite).2 <| Stacks.Algebraization.HasProperSupport.C1573.of_iso _ eΦ.symm
      (Stacks.Algebraization.HasProperSupport.C1573.of_eq hq.symm hFV)
  · have hc := isIso_chartCompletionHom B (Spec (.of A)) hA
      (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩)
      (idEtaleChart B (Spec (.of A)) hA U)
      (baseIdealSubmodule (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) I)
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (B.inclusion.map U.hom)) hK F hF hIcart
    let c := @asIso _ _ _ _ _ hc
    let eC : chartCoherentModuleOf B (Spec (.of A)) hA
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩)
        (idEtaleChart B (Spec (.of A)) hA U) F hF ≅ FV :=
      (ObjectProperty.fullyFaithfulι _).preimageIso eΦ
    let e1 := (ObjectProperty.ι _).mapIso
      ((Stacks.Algebraization.completionFunctor _ _).mapIso eC ≪≫ eV)
    let eSys := c.symm ≪≫ e1
    let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B (Spec (.of A)) hA
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩)
    have hFF := chartZariskiModuleFullyFaithfulIdEtaleChart B (Spec (.of A)) hA U
    let Aq := P.lift (adicQuotientSystem B (Spec (.of A)) hA (yoneda.obj U)
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
        (baseIdealSubmodule (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) I) F)
      (fun n => ((isCoherentAdicSystem_adicQuotientSystem B (Spec (.of A)) hA _ _ _ hIqc F
        hF).1 n.unop).toIsQuasicoherentOnSite)
    let Gq := P.lift G.obj (fun n => (G.property.1 n.unop).toIsQuasicoherentOnSite)
    let eq' : Aq ⋙ (P.ι ⋙ chartZariskiModule B (Spec (.of A)) hA
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩
        (idEtaleChart B (Spec (.of A)) hA U)) ≅
      Gq ⋙ (P.ι ⋙ chartZariskiModule B (Spec (.of A)) hA
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩
        (idEtaleChart B (Spec (.of A)) hA U)) := eSys
    exact ⟨(Functor.isoWhiskerRight ((hFF.whiskeringRight ℕᵒᵖ).preimageIso eq') P.ι).symm⟩

end AlgebraicGeometry.Space

end

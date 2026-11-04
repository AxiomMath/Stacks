module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionGenus
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionNodal
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PushoutContraction
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructurePushforward
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Iterated
public import StacksFrontier.Topology.Sober.SurjectionComponents

/-!
# Successive contractions of rational bridges

Let `k` be a field and `X` a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and `H⁰(X, 𝒪_X) = k`. The target `Y` of the contraction `c : X ⟶ Y` of a rational
bridge of `X` again has all of these properties and the genus of `X`, and `𝒪_Y = c_*𝒪_X`,
`Rⁱ c_*𝒪_X = 0` for `i > 0`. This file iterates these facts along a chain
`X = X₀ → X₁ → ⋯ → Xₙ` of contractions of rational bridges, as recorded by
`AlgebraicGeometry.IsIteratedContractionOfRationalBridges`, and shows that rational bridges can
be contracted until none are left: each contraction lowers the number of irreducible components.

## Main results

* `Stacks.Curves.structureMorphism_eq_of_isContractionOfRationalBridge`: the structure morphism
  of the target of a contraction over `k` is unique.
* `Stacks.Curves.hasAtWorstNodalSingularities_of_isContractionOfRationalBridge`: the target of any
  contraction of a rational bridge, over `k` compatibly with the contraction, is at worst nodal.
* `Stacks.Curves.exists_iso_pushoutScheme_of_isContractionOfRationalBridge`: the target of any
  contraction is isomorphic to the chosen pushout, compatibly with the structure morphisms.
* `Stacks.Curves.ncard_irreducibleComponents_lt_of_isContractionOfRationalBridge`: a contraction
  of a rational bridge lowers the number of irreducible components.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.standing_target`: the hypotheses on
  `X` and the genus pass along a chain, and the composite `c` satisfies `𝒪_Y = c_*𝒪_X` and
  `Rⁱ c_*𝒪_X = 0` for `i > 0`.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.exists_forall_not_isRationalBridge`:
  rational bridges can be contracted until none are left.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- Two morphisms to an affine scheme agree if they agree after precomposition with a morphism
that is an isomorphism on global sections. -/
private theorem eq_of_comp_eq_of_isIso_appTop {A B : Scheme.{u}} {R : CommRingCat.{u}}
    {f : A ⟶ B} [IsIso f.appTop] {g g' : B ⟶ Spec R} (h : f ≫ g = f ≫ g') : g = g' := by
  refine ext_of_isAffine ((cancel_mono f.appTop).1 ?_)
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h]

/-- Two structure morphisms `g g' : Y ⟶ Spec k` of the target of a contraction `c : X ⟶ Y` of a
rational bridge with `c ≫ g = c ≫ g'` are equal. -/
theorem structureMorphism_eq_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {g g' : Y ⟶ Spec (.of k)} (h : c ≫ g = c ≫ g') :
    g = g' := by
  have := isIso_appTop_of_isContractionOfRationalBridge hdim hnodal hc
  exact eq_of_comp_eq_of_isIso_appTop h

/-- For any contraction
`c : X ⟶ Y` of a rational bridge and any structure morphism `g` of `Y` over `k` compatible with
`c`, there is an isomorphism from the chosen pushout `pushoutScheme (bridgePushoutSituation …)`
to `Y` which carries the canonical map from the closure `X'` of the complement to the restriction
of `c` to `X'`, and the structure morphism `pushoutToBase` to `g`. -/
theorem exists_iso_pushoutScheme_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {g : Y ⟶ Spec (.of k)}
    (hcg : c ≫ g = X ↘ Spec (.of k)) :
    ∃ e : pushoutScheme (bridgePushoutSituation hdim hnodal hC) ≅ Y,
      pushoutInl (bridgePushoutSituation hdim hnodal hC) ≫ e.hom = complementaryCurveι C ≫ c ∧
      e.hom ≫ g = pushoutToBase (bridgePushoutSituation hdim hnodal hC) := by
  let s := bridgePushoutSituation hdim hnodal hC
  obtain ⟨-, a, b, hpo, hac, hbc⟩ := id hc
  have hpos : IsPushout s.i s.j a b := hpo
  let e : pushoutScheme s ≅ Y :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout s.X s.Y hpos
  have hia : pushoutInl s ≫ e.hom = a :=
    IsPushout.inl_isoIsPushout_hom s.X s.Y (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos
  have hib : pushoutInr s ≫ e.hom = b :=
    IsPushout.inr_isoIsPushout_hom s.X s.Y (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos
  refine ⟨e, hia.trans hac.symm, ?_⟩
  refine (pushoutAlongClosedImmersionAndIntegral s).isPushout.hom_ext ?_ ?_
  · show pushoutInl s ≫ e.hom ≫ g = pushoutInl s ≫ pushoutToBase s
    rw [reassoc_of% hia, ← hac]
    exact (Category.assoc _ _ _).trans ((congrArg _ hcg).trans
      (pushoutInl_comp_pushoutToBase_bridge hdim hnodal hC).symm)
  · show pushoutInr s ≫ e.hom ≫ g = pushoutInr s ≫ pushoutToBase s
    rw [reassoc_of% hib, show pushoutInr s ≫ pushoutToBase s = s.pY by simp [pushoutToBase]]
    have hC' : C.subscheme.toSpecΓ ≫ b ≫ g = C.subscheme.toSpecΓ ≫ s.pY := by
      rw [← Category.assoc, ← hbc, Category.assoc, hcg]
      exact (toSpecΓ_comp_bridgeSectionsStructureMap C).symm
    have : IsIso C.subscheme.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance
    exact eq_of_comp_eq_of_isIso_appTop (f := C.subscheme.toSpecΓ) hC'

/-- The target of a contraction `c : X ⟶ Y` of a rational bridge has at-worst-nodal
singularities over `k`, for any structure morphism `g : Y ⟶ Spec k` with `c ≫ g` the structure
morphism of `X`. -/
theorem hasAtWorstNodalSingularities_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {g : Y ⟶ Spec (.of k)}
    (hcg : c ≫ g = X ↘ Spec (.of k)) :
    letI : Y.Over (Spec (.of k)) := ⟨g⟩
    HasAtWorstNodalSingularities k Y := by
  let : Y.Over (Spec (.of k)) := ⟨g⟩
  obtain ⟨e, -, heg⟩ := exists_iso_pushoutScheme_of_isContractionOfRationalBridge hdim hnodal hc hcg
  let p : pushoutScheme (bridgePushoutSituation hdim hnodal hC) ⟶ Spec (.of k) :=
    pushoutToBase (bridgePushoutSituation hdim hnodal hC)
  have hP : let : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
      ⟨p⟩
      HasAtWorstNodalSingularities k (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) :=
    hasAtWorstNodalSingularities_pushoutScheme_bridge hdim hnodal hC
  have : LocallyOfFiniteType p := locallyOfFiniteType_pushoutToBase_bridge hdim hnodal hC
  have heg' : e.hom ≫ g = p := heg
  have hg : g = e.inv ≫ p := by rw [← heg']; simp
  have : LocallyOfFiniteType g := by rw [hg]; infer_instance
  have hPdim := topologicalKrullDim_pushoutScheme_bridge hdim hnodal hC
  have hYdim : topologicalKrullDim Y = 1 := by
    rw [← hPdim]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
  intro y hy
  have hyc : IsClosed ({e.inv.base y} :
      Set (pushoutScheme (bridgePushoutSituation hdim hnodal hC))) := by
    have h := e.inv.homeomorph.isClosedMap _ hy
    rwa [Set.image_singleton] at h
  have h := smoothAt_or_isNode_of_etale_of_comm k p g hPdim hYdim (𝟙 _) e.hom
    (by rw [heg', Category.id_comp]) (e.inv.base y) (hP _ hyc)
  have hy' : e.hom.base (e.inv.base y) = y := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rwa [hy'] at h

/-- The target of a contraction of a rational bridge of `X` has fewer irreducible components
than `X`. -/
theorem ncard_irreducibleComponents_lt_of_isContractionOfRationalBridge
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    (irreducibleComponents Y).ncard < (irreducibleComponents X).ncard := by
  let s := bridgePushoutSituation hdim hnodal hC
  obtain ⟨g, hcg, -⟩ := exists_isProper_structureMorphism_contraction_bridge hdim hnodal hc
  obtain ⟨e, hea, -⟩ := exists_iso_pushoutScheme_of_isContractionOfRationalBridge hdim hnodal hc hcg
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian (complementaryCurve C) :=
    LocallyOfFiniteType.isLocallyNoetherian (complementaryCurveι C)
  have : CompactSpace (complementaryCurve C) :=
    QuasiCompact.compactSpace_of_compactSpace (complementaryCurveι C)
  have : IsNoetherian (complementaryCurve C) := ⟨⟩
  have hdom : IsSchemeTheoreticallyDominant
      (Scheme.IdealSheafData.inclusion (I := C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
        C.subscheme.toSpecΓ) := by
    have := hC.isIntegral
    let : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    have : Nonempty (intersectionWithComplementaryCurve C) := nonempty_intersection_bridge hC
    have : Subsingleton (Spec Γ(C.subscheme, ⊤) : Type u) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)))
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  have hsj : IsSchemeTheoreticallyDominant s.j := hdom
  have : Surjective (pushoutInl s) := pushoutInl_surjective s
  have : Surjective (pushoutInl s ≫ e.hom) := inferInstance
  calc (irreducibleComponents Y).ncard
      ≤ (irreducibleComponents (complementaryCurve C)).ncard :=
        (ncard_irreducibleComponents_le_of_surjective _ (pushoutInl s ≫ e.hom).continuous
          Surjective.surj
          (NoetherianSpace.finite_irreducibleComponents (α := complementaryCurve C))).2
    _ < (irreducibleComponents X).ncard :=
        ncard_irreducibleComponents_complementaryCurve_lt C hC.support_mem_irreducibleComponents

end Stacks.Curves

namespace AlgebraicGeometry.IsIteratedContractionOfRationalBridges

variable {k : Type u} [Field k]

/-- Along a chain `c : X ⟶ Y` of contractions of rational bridges, starting from a curve `X`
proper over `k`, of dimension one, with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, the
target `Y` has the same four properties and the same genus, and `c` satisfies `𝒪_Y = c_*𝒪_X` and
`Rⁱ c_*𝒪_X = 0` for `i > 0`. -/
theorem standing_target {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} (hseq : IsIteratedContractionOfRationalBridges k fX fY c)
    (hproper : IsProper fX) (hdim : topologicalKrullDim X = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsProper fY ∧ topologicalKrullDim Y = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) ∧
      @Stacks.Curves.HasAtWorstNodalSingularities k _ Y ⟨fY⟩ ∧
      genus fY = genus fX ∧
      IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  induction hseq with
  | identity X fX =>
    refine ⟨hproper, hdim, hglobal, hnodal, rfl, ?_, fun i hi => ?_⟩
    · exact isIso_unitToPushforwardObjUnit_of_forall_isIso_app _ fun W =>
        Functor.map_isIso (forget₂ CommRingCat RingCat) ((𝟙 X : X ⟶ X).app W.unop)
    · have : (Scheme.Modules.pushforward (𝟙 X)).IsEquivalence :=
        Functor.IsEquivalence.mk' (Scheme.Modules.pushforward (𝟙 X))
          (Scheme.Modules.pushforwardComp (𝟙 X) (𝟙 X) ≪≫
            Scheme.Modules.pushforwardCongr (Category.id_comp _) ≪≫
            Scheme.Modules.pushforwardId X).symm
          (Scheme.Modules.pushforwardComp (𝟙 X) (𝟙 X) ≪≫
            Scheme.Modules.pushforwardCongr (Category.id_comp _) ≪≫
            Scheme.Modules.pushforwardId X)
      exact Functor.isZero_rightDerived_of_exact _ _ i hi
  | @step X Y Z fX fY fZ c d C hC hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
    obtain ⟨hCb, hc⟩ := hC hproper
    obtain ⟨g, hcg, hgp, hgdim, hgglob, hggenus⟩ :=
      Stacks.Curves.exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim
        hnodal C hCb c hc
    have hfY : fY = g := Stacks.Curves.structureMorphism_eq_of_isContractionOfRationalBridge
      hdim hnodal hc (hbase.trans hcg.symm)
    subst hfY
    have hYnodal := Stacks.Curves.hasAtWorstNodalSingularities_of_isContractionOfRationalBridge
      hdim hnodal hc hcg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih hgp hgdim hgglob hYnodal
    have hcO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) :=
      Stacks.Curves.isIso_structureSheafToPushforward_contraction_bridge hdim hnodal hc
    have hcR : ∀ i : ℕ, 0 < i → Limits.IsZero
        (((Scheme.Modules.pushforward c).rightDerived i).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
      fun i hi => Stacks.Curves.rightAcyclic_pushforward_ambientStructureSheaf_bridge hdim hnodal
        hc i hi
    have : IsProper c := by
      have : IsProper (c ≫ fY) := by rw [hcg]; exact hproper
      exact IsProper.of_comp c fY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
    refine ⟨h1, h2, h3, h4, h5.trans hggenus, ?_, fun i hi => ?_⟩
    · exact Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp _ _ hcO h6
    · exact (h7 i hi).of_iso (Stacks.Curves.StableModel.rightDerivedCompUnitIso c d hcO hcR i)

variable {X : Scheme.{u}} {fX : X ⟶ Spec (.of k)} [IsProper fX]
  (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
  (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X)

include hdim hnodal

/-- A proper one-dimensional curve over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities admits a chain of contractions of rational bridges whose target is proper over `k`
and has no rational bridge. -/
theorem exists_forall_not_isRationalBridge :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k)) (c : X ⟶ Y),
      IsIteratedContractionOfRationalBridges k fX fY c ∧ IsProper fY ∧
        ∀ C : Y.IdealSheafData,
          letI : Y.Over (Spec (.of k)) := ⟨fY⟩
          ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C := by
  suffices h : ∀ (n : ℕ) (X : Scheme.{u}) (fX : X ⟶ Spec (.of k)),
      (irreducibleComponents X).ncard = n → IsProper fX → topologicalKrullDim X = 1 →
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop) →
      @Stacks.Curves.HasAtWorstNodalSingularities k _ X ⟨fX⟩ →
      ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k)) (c : X ⟶ Y),
        IsIteratedContractionOfRationalBridges k fX fY c ∧ IsProper fY ∧
          ∀ C : Y.IdealSheafData,
            let : Y.Over (Spec (.of k)) := ⟨fY⟩
            ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C from
    h _ X fX rfl inferInstance hdim inferInstance hnodal
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X fX hn hproper hdim hglobal hnodal
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  have : IsProper (X ↘ Spec (.of k)) := hproper
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
  by_cases hbridge : ∃ C : X.IdealSheafData, IsRationalBridge k X C
  · obtain ⟨C, hC⟩ := hbridge
    obtain ⟨Y, c, hc⟩ := Stacks.Curves.exists_pushout_contraction_bridge hdim hnodal hC
    obtain ⟨g, hcg, hgp, hgdim, hgglob, -⟩ :=
      Stacks.Curves.exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim
        hnodal C hC c hc
    have hYnodal := Stacks.Curves.hasAtWorstNodalSingularities_of_isContractionOfRationalBridge
      hdim hnodal hc hcg
    have hlt := Stacks.Curves.ncard_irreducibleComponents_lt_of_isContractionOfRationalBridge
      hdim hnodal hc
    obtain ⟨Z, fZ, d, hd, hZp, hZ⟩ := ih _ (hn ▸ hlt) Y g rfl hgp hgdim hgglob hYnodal
    exact ⟨Z, fZ, c ≫ d, .step C (fun _ => ⟨hC, hc⟩) hcg hd, hZp, hZ⟩
  · push Not at hbridge
    exact ⟨X, fX, 𝟙 X, .identity X fX, hproper, fun C _ => hbridge C⟩

end AlgebraicGeometry.IsIteratedContractionOfRationalBridges

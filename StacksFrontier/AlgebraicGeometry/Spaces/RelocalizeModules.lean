module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeCostructuredArrow

/-!
# Modules on an algebraic space viewed over a larger base

Let `g : T ⟶ S` be a morphism of a big fppf site and let `X` be an algebraic space over `T`. Its
lower-shriek extension `Λ X = OverShriek.relocalizePresheafFunctor g X` is an algebraic space over
`S` (Stacks 03I5 (2), `AlgebraicGeometry.Space.isAlgebraicSpace_relocalize`), the same space viewed
over the larger base. The étale charts of the two are the same schemes: a chart `(U, x)` of `X`
gives the chart `(U, (U ⟶ T, x))` of `Λ X` and every chart of `Λ X` is of this form. So the small
étale sites are equivalent, by an equivalence which does not change the scheme underlying a chart;
it matches the two small étale topologies and the two structure sheaves, and so identifies the
`𝒪`-modules of `X` with those of `Λ X`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.relocalize`: the equivalence of small étale sites.
* `AlgebraicGeometry.Space.relocalizeModulesEquivalence`: the equivalence
  `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})` of the categories of modules.

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_relocalizeChart_iff`: a scheme chart of `X` is étale if
  and only if the attached chart of `Λ X` is.
* `AlgebraicGeometry.Space.SmallEtale.relocalize_functor_isDenseSubsite` and
  `AlgebraicGeometry.Space.SmallEtale.relocalize_inverse_isDenseSubsite`: the equivalence is an
  equivalence of sites.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_relocalizeModulesEquivalence_iff`:
  quasi-coherence is preserved and reflected.
* `AlgebraicGeometry.Space.isFinitePresentation_relocalizeModulesEquivalence_functor_iff` and
  `AlgebraicGeometry.Space.isFinitePresentation_relocalizeModulesEquivalence_inverse`: finite
  presentation is preserved and reflected.

## Implementation notes

The equivalence of module categories is `Stacks.SheafOfModules.reindexEquivalence` along the
equivalence of sites, so its inverse is the direct image along `SmallEtale.relocalize`. Its
functor is identified with the direct image along the inverse equivalence
(`AlgebraicGeometry.Space.relocalizeModulesEquivalenceSymmFunctorIso`): the structure map of that
second reindexing is the identity, the counit of the equivalence of sites having identity
underlying morphisms of schemes. Each direction is then a pullback along a morphism of ringed
topoi, which is what carries finite presentation (Stacks 03DO).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)

/-- The étale-chart condition is a condition on underlying morphisms of schemes, which
`Over.map g` does not change. -/
private lemma etale_overMap_iff {a b : BigFppfOver B T hT} (k : a ⟶ b) :
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ((Over.map g).map k) ↔
      MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B T hT) k :=
  Iff.rfl

private instance : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).RespectsIso := by
  have : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- **A scheme chart of `X` is étale exactly when the attached chart of `Λ X` is.** The chart of
`Λ X` is `Λ` of the chart of `X` read through `h_{j U} ≅ Λ h_U`, and `Λ` preserves and reflects
the property of having étale represented base changes; reflection uses that a morphism from a
representable presheaf to an algebraic space is representable. -/
theorem isEtaleChart_relocalizeChart_iff (hX : IsAlgebraicSpace B T hT X)
    (A : CostructuredArrow yoneda X) :
    IsEtaleChart B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        ((OverShriek.relocalizeChart g X).obj A) ↔ IsEtaleChart B T hT X A := by
  show MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (yonedaEquiv.symm (OverShriek.relocalizeChartSection g X A)) ↔ _
  rw [OverShriek.relocalizeChart_hom, ← OverShriek.relocalizeYonedaFactorIso_hom]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).trans
    ⟨OverShriek.presheaf_of_presheaf_map_relocalize g (fun k => (etale_overMap_iff B hT hS g k).1)
      (Functor.relativelyRepresentable.diag_iff.mp hX.diagonal_representable A.hom),
    OverShriek.presheaf_map_relocalize g (fun k => (etale_overMap_iff B hT hS g k).2)⟩

namespace SmallEtale

variable (hX : IsAlgebraicSpace B T hT X)

/-- **The small étale site of `X` is the small étale site of `Λ X`**: the equivalence of scheme
charts of `OverShriek.relocalizeChartEquivalence` restricts to the étale charts. -/
noncomputable def relocalize :
    SmallEtale B T hT X ≌ SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X) :=
  Equivalence.congrFullSubcategory (OverShriek.relocalizeChartEquivalence g X)
    (funext fun A => propext (isEtaleChart_relocalizeChart_iff B hT hS g X hX A))

/-- The equivalence does not change the scheme underlying a chart. -/
theorem relocalize_functor_comp_toSchemes :
    (relocalize B hT hS g X hX).functor ⋙ toSchemes B S hS _ = toSchemes B T hT X :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The inverse equivalence does not change the scheme underlying a chart. -/
theorem relocalize_inverse_comp_toSchemes :
    (relocalize B hT hS g X hX).inverse ⋙ toSchemes B T hT X = toSchemes B S hS _ :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- A functor of small étale sites which keeps covering families of charts covering is cover
preserving. -/
private theorem coverPreserving_of_isCovering {T' S' : Scheme.{u}} {hT' : B.Contains T'}
    {hS' : B.Contains S'}
    {Y : (BigFppfOver B T' hT')ᵒᵖ ⥤ Type u} {Z : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (F : SmallEtale B T' hT' Y ⥤ SmallEtale B S' hS' Z) [F.IsEquivalence]
    (hF : ∀ {A} (E : PreZeroHypercover.{u + 1} A), IsCovering B T' hT' Y ⟨A, E⟩ →
      IsCovering B S' hS' Z ⟨F.obj A, E.map F⟩) :
    CoverPreserving (topology B T' hT' Y) (topology B S' hS' Z) F := by
  refine coverPreserving_of_generators F (precoverage B T' hT' Y) _ ?_
  intro A R hR
  obtain ⟨E, rfl, hE⟩ := (mem_precoverage_iff B T' hT' Y).mp hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  refine Precoverage.generate_mem_toGrothendieck ?_
  refine (mem_precoverage_iff B S' hS' Z).2 ⟨E.map F, ?_, hF E hE⟩
  simp [PreZeroHypercover.presieve₀_map]

/-- The equivalence carries covering families of charts to covering families of charts. -/
theorem relocalize_functor_coverPreserving :
    CoverPreserving (topology B T hT X) (topology B S hS _)
      (relocalize B hT hS g X hX).functor :=
  coverPreserving_of_isCovering B _ fun _ => id

/-- The inverse equivalence carries covering families of charts to covering families of
charts. -/
theorem relocalize_inverse_coverPreserving :
    CoverPreserving (topology B S hS _) (topology B T hT X)
      (relocalize B hT hS g X hX).inverse :=
  coverPreserving_of_isCovering B _ fun _ => id

/-- The inverse equivalence of small étale sites is cocontinuous. -/
instance relocalize_inverse_isCocontinuous :
    (relocalize B hT hS g X hX).inverse.IsCocontinuous (topology B S hS _) (topology B T hT X) :=
  (((relocalize B hT hS g X hX).symm).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (relocalize_functor_coverPreserving B hT hS g X hX)

/-- The equivalence of small étale sites is cocontinuous. -/
instance relocalize_functor_isCocontinuous :
    (relocalize B hT hS g X hX).functor.IsCocontinuous (topology B T hT X) (topology B S hS _) :=
  ((relocalize B hT hS g X hX).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (relocalize_inverse_coverPreserving B hT hS g X hX)

/-- The equivalence of small étale sites is continuous. -/
instance relocalize_functor_isContinuous :
    (relocalize B hT hS g X hX).functor.IsContinuous (topology B T hT X) (topology B S hS _) :=
  Functor.isContinuous_iff_coverPreserving.2 (relocalize_functor_coverPreserving B hT hS g X hX)

/-- The inverse equivalence of small étale sites is continuous. -/
instance relocalize_inverse_isContinuous :
    (relocalize B hT hS g X hX).inverse.IsContinuous (topology B S hS _) (topology B T hT X) :=
  Functor.isContinuous_iff_coverPreserving.2 (relocalize_inverse_coverPreserving B hT hS g X hX)

/-- The equivalence of small étale sites is a dense subsite. -/
instance relocalize_functor_isDenseSubsite :
    (relocalize B hT hS g X hX).functor.IsDenseSubsite (topology B T hT X) (topology B S hS _) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ (relocalize B hT hS g X hX)

/-- The inverse equivalence of small étale sites is a dense subsite. -/
instance relocalize_inverse_isDenseSubsite :
    (relocalize B hT hS g X hX).inverse.IsDenseSubsite (topology B S hS _) (topology B T hT X) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (relocalize B hT hS g X hX)

/-- The structure presheaf of `X` is that of `Λ X` restricted along the equivalence. -/
theorem relocalize_functor_op_comp_structurePresheaf :
    (relocalize B hT hS g X hX).functor.op ⋙ structurePresheaf B S hS _ =
      structurePresheaf B T hT X :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

end SmallEtale

variable (hX : IsAlgebraicSpace B T hT X)

include hX in
/-- `Λ X` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_relocalize' :
    IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor g).obj X) :=
  isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g X hX

/-- The structure sheaf of rings of `Λ X`, typed at the small étale topology. -/
noncomputable abbrev relocalizeRingSheaf :
    Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))
      RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)).O)

/-- The structure sheaf of rings of `X` is that of `Λ X` transported along the equivalence of
small étale sites. -/
theorem reindexRing_relocalize :
    Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
        (SmallEtale.relocalize B hT hS g X hX)
        (relocalizeRingSheaf B hT hS g X hX) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X hX).O) :=
  rfl

/-- **The `𝒪`-modules of `X` are the `𝒪`-modules of `Λ X`**: transport along the equivalence of
small étale ringed sites. -/
noncomputable def relocalizeModulesEquivalence :
    Modules.{u, u} B T hT X hX ≌
      Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX) :=
  (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B T hT X)
    (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX)).symm

/-- **Quasi-coherence is invariant under the equivalence.** -/
theorem isQuasicoherentOnSite_relocalizeModulesEquivalence_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff (J' := SmallEtale.topology B T hT X)
    (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX) M

/-- `Type u` has limits indexed by the structured arrows from `W` to the opposite of the inverse
equivalence of small étale sites. -/
instance hasLimitsOfShape_structuredArrow_relocalize_inverse
    (W : (SmallEtale B T hT X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (SmallEtale.relocalize B hT hS g X hX).inverse.op)
      (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (SmallEtale.relocalize B hT hS g X hX).inverse.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The inverse equivalence of small étale sites is a morphism of sites. -/
instance relocalize_inverse_isMorphismOfSites :
    IsMorphismOfSites.{u} (SmallEtale.relocalize B hT hS g X hX).inverse
      (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- **Finite presentation is carried from `Λ X` to `X`.** -/
theorem isFinitePresentation_relocalizeModulesEquivalence_inverse
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) (hM : M.IsFinitePresentation) :
    ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M).IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_reindexEquivalence_functor_obj
    (SmallEtale.topology B T hT X)
    (SmallEtale.relocalize B hT hS g X hX) (structureSheaf B S hS _
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) M hM

/-- The counit of the equivalence of small étale sites, read in `X`, is the identity on
underlying schemes, so the structure sheaf sends it to the identity. -/
theorem structurePresheaf_map_relocalize_unitInv (U : SmallEtale B T hT X) :
    (structurePresheaf B T hT X).map ((SmallEtale.relocalize B hT hS g X hX).unitInv.app U).op =
      𝟙 _ := by
  show Scheme.Γ.map (𝟙 _).op = 𝟙 _
  rw [op_id, Scheme.Γ.map_id]

/-- The functor of the symmetric equivalence of small étale sites is continuous. -/
instance relocalize_symm_functor_isContinuous :
    (SmallEtale.relocalize B hT hS g X hX).symm.functor.IsContinuous
      (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X) :=
  inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).inverse.IsContinuous _ _)

/-- The inverse of the symmetric equivalence of small étale sites is continuous. -/
instance relocalize_symm_inverse_isContinuous :
    (SmallEtale.relocalize B hT hS g X hX).symm.inverse.IsContinuous
      (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _) :=
  inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsContinuous _ _)

/-- The inverse of the symmetric equivalence of small étale sites is a dense subsite. -/
instance relocalize_symm_inverse_isDenseSubsite :
    (SmallEtale.relocalize B hT hS g X hX).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _) :=
  inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsDenseSubsite _ _)

/-- The structure sheaf of rings of `X`, typed at the small étale topology. -/
noncomputable abbrev relocalizeBaseRingSheaf :
    Sheaf (SmallEtale.topology B T hT X) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X hX).O)

/-- The structure map of the reindexing along the inverse equivalence is the identity. -/
theorem reindexBackSharp_relocalize_symm :
    Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B T hT X)
        (J' := SmallEtale.topology B S hS _) (SmallEtale.relocalize B hT hS g X hX).symm
        (relocalizeBaseRingSheaf B hT X hX) = 𝟙 (relocalizeBaseRingSheaf B hT X hX) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  show (forget₂ CommRingCat RingCat).map ((structurePresheaf B T hT X).map
    ((SmallEtale.relocalize B hT hS g X hX).unitInv.app U.unop).op) = 𝟙 _
  rw [structurePresheaf_map_relocalize_unitInv]
  exact (forget₂ CommRingCat RingCat).map_id _

/-- The reindexing of `𝒪_X`-modules along the inverse equivalence of small étale sites, an
equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})` whose functor is the direct image along that inverse. -/
noncomputable def relocalizeModulesEquivalenceSymm :
    Modules.{u, u} B T hT X hX ≌
      Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX) :=
  Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS _)
    (SmallEtale.relocalize B hT hS g X hX).symm (relocalizeBaseRingSheaf B hT X hX)

/-- The two equivalences have the same inverse functor. -/
theorem relocalizeModulesEquivalenceSymm_inverse :
    (relocalizeModulesEquivalenceSymm B hT hS g X hX).inverse =
      (relocalizeModulesEquivalence B hT hS g X hX).inverse := by
  show SheafOfModules.pushforward _ = SheafOfModules.pushforward _
  rw [reindexBackSharp_relocalize_symm]
  rfl

/-- The functors of the two equivalences are isomorphic, being left adjoint to the same
functor. -/
noncomputable def relocalizeModulesEquivalenceSymmFunctorIso :
    (relocalizeModulesEquivalenceSymm B hT hS g X hX).functor ≅
      (relocalizeModulesEquivalence B hT hS g X hX).functor :=
  Adjunction.leftAdjointUniq (relocalizeModulesEquivalenceSymm B hT hS g X hX).toAdjunction
    ((relocalizeModulesEquivalence B hT hS g X hX).toAdjunction.ofNatIsoRight
      (eqToIso (relocalizeModulesEquivalenceSymm_inverse B hT hS g X hX).symm))

/-- `Type u` has limits indexed by the structured arrows from `W` to the opposite of the inverse
of the symmetric equivalence of small étale sites. -/
instance hasLimitsOfShape_structuredArrow_relocalize_functor
    (W : (SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (SmallEtale.relocalize B hT hS g X hX).symm.inverse.op)
      (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (SmallEtale.relocalize B hT hS g X hX).symm.inverse.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The inverse of the symmetric equivalence of small étale sites is a morphism of sites. -/
instance relocalize_symm_inverse_isMorphismOfSites :
    IsMorphismOfSites.{u} (SmallEtale.relocalize B hT hS g X hX).symm.inverse
      (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- **Finite presentation is carried from `X` to `Λ X`.** -/
theorem isFinitePresentation_relocalizeModulesEquivalence_functor
    (N : Modules.{u, u} B T hT X hX) (hN : N.IsFinitePresentation) :
    ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj N).IsFinitePresentation :=
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((relocalizeModulesEquivalenceSymmFunctorIso B hT hS g X hX).app N)
    (Stacks.SheafOfModules.isFinitePresentation_reindexEquivalence_functor_obj
      (SmallEtale.topology B S hS _)
      (SmallEtale.relocalize B hT hS g X hX).symm (structureSheaf B T hT X hX) N hN)

/-- **Finite presentation is invariant under the equivalence.** -/
theorem isFinitePresentation_relocalizeModulesEquivalence_functor_iff
    (N : Modules.{u, u} B T hT X hX) :
    ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj N).IsFinitePresentation ↔
      N.IsFinitePresentation :=
  ⟨fun h => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app N).symm
      (isFinitePresentation_relocalizeModulesEquivalence_inverse B hT hS g X hX _ h),
    isFinitePresentation_relocalizeModulesEquivalence_functor B hT hS g X hX N⟩

end AlgebraicGeometry.Space

end

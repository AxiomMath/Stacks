module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresentsCounterexample
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityCase2
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# Stacks 0GHE: the statement decided

In Situation 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`) the online version of
**Stacks 0GHE** reads

> assume given a closed subset `Z ⊂ S` such that (1) the inverse image of `Z` in `X'` is `T'`,
> (2) `U' → S ∖ Z` is a closed immersion, (3) `W → S_{/Z}` is a closed immersion. Then there
> exists a solution `(f : X' → X, T, a)` and moreover `X → S` is a closed immersion.

The proof in the source uses the hypothesis that `X' → S` is proper (the theorem on formal
functions, applied to `X' → S`), which the statement omits. Without that hypothesis the
lemma is false: if `X → S` is a closed immersion and `f : X' → X` is proper, then
`X' → X → S` is proper
(`AlgebraicGeometry.Artin.ContractionSituation.isProper_terminal_from_X'_of_solution`),
so properness of `X' → S` is a *necessary* condition for the conclusion, and it does not follow
from (1)–(3).

The counterexample (`AlgebraicGeometry.Artin.ContractionSituation.openSituation`) works over
every locally Noetherian scheme `S` with an open subset `O` that is not closed (for instance
`S = 𝔸¹_k` and `O = 𝔾_m = 𝔸¹_k ∖ {0}`): take `X' = O`, `T' = ∅`, `W = X'_{/T'}` (the empty
formal space), `g = id` and `Z = S ∖ O`. Then the inverse image of `Z` in `X'` is empty, `U' = O`
maps isomorphically onto `S ∖ Z = O`, and `W` is empty, so (1)–(3) hold; but `X' = O → S` is
not proper since its image is not closed.

## Main results

* `exists_solution_of_isClosedImmersion_and_not_forall`:
  **Stacks 0GHE**, decided: the lemma under the hypothesis that `X' → S` is proper, and the
  failure of the statement without it over every locally Noetherian `S` having a closed subset
  which is not open.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Properness of `X' → S` is necessary -/

/-- **Properness of `X' → S` is necessary for the conclusion of Stacks 0GHE.** If a solution
`(f : X' → X, T, a)` has `X → S` a closed immersion, then `X' → S` is proper: it is the
composite of the proper morphism `f` with the closed immersion `X → S`. -/
theorem isProper_terminal_from_X'_of_solution (c : ContractionSituation B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (s : c.Solution X)
    (hX : Space.IsClosedImmersion B S hS (terminal.from X)) :
    Space.IsProper B S hS (terminal.from c.X') := by
  have hT := Space.isAlgebraicSpace_terminal B S hS
  rw [show terminal.from c.X' = s.f ≫ terminal.from X from terminal.hom_ext _ _]
  exact Space.isProper_comp' B S hS s.f (terminal.from X) s.isAlgebraicSpace_X hT s.isProper_f
    (Space.isProper_of_isClosedImmersion B S hS s.isAlgebraicSpace_X hT _ hX)

/-- If a solution has `X → S` a closed immersion, then the image of `|X'| → |S|` is closed. -/
theorem isClosed_range_pointsMap_terminal_from_X'_of_solution (c : ContractionSituation B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (s : c.Solution X)
    (hX : Space.IsClosedImmersion B S hS (terminal.from X)) :
    IsClosed (Set.range (Space.pointsMap B S hS c.X' (terminal.from c.X'))) :=
  (Space.isClosedMap_pointsMap_of_universallyClosed (Space.isAlgebraicSpace_terminal B S hS) _
    (isProper_terminal_from_X'_of_solution c s hX).universallyClosed).isClosed_range

/-! ### The base and its open subschemes as objects of the site -/

variable (B S hS) in
/-- The Yoneda presheaf of `S`, as an object of the big fppf site over itself, is the terminal
presheaf. -/
noncomputable def baseYonedaIso :
    yoneda.obj (baseSiteObject B S hS) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

variable (B S hS) in
/-- The point space of the terminal presheaf is homeomorphic to `S`. -/
noncomputable def terminalPointsHomeomorph :
    Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ≃ₜ S :=
  (Space.pointsHomeomorphOfIso B S hS (baseYonedaIso B S hS).symm).trans
    (Space.schemePointsHomeomorph B S hS (baseSiteObject B S hS))

variable (B S hS) in
/-- The open subscheme `O ⊆ S`, as an object of the big fppf site over `S`. -/
noncomputable abbrev openSiteObject (O : S.Opens) : BigFppfOver B S hS :=
  Space.openSub (baseSiteObject B S hS) O

/-- The structure morphism of the open subscheme `O ⊆ S`, as a morphism of presheaves to the
terminal presheaf. -/
noncomputable abbrev openToTerminal (O : S.Opens) :
    yoneda.obj (openSiteObject B S hS O) ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  yoneda.map (Space.openSubHom (baseSiteObject B S hS) O) ≫ (baseYonedaIso B S hS).hom

/-- The structure morphism of the open subscheme `O ⊆ S` is an open immersion. -/
theorem isOpenImmersion_openToTerminal (O : S.Opens) :
    Space.IsOpenImmersion B S hS (openToTerminal (B := B) (hS := hS) O) :=
  MorphismProperty.RespectsIso.postcomp _ _ _
    (Space.isOpenImmersion_yoneda_map_openSubHom (baseSiteObject B S hS) O)

/-- On points, the structure morphism of `O ⊆ S` is the inclusion of `O`. -/
theorem terminalPointsHomeomorph_pointsMap_openToTerminal (O : S.Opens)
    (x : (BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS O)) :
    terminalPointsHomeomorph B S hS (Space.pointsMap B S hS _ (openToTerminal O)
      ((Space.schemePointsHomeomorph B S hS (openSiteObject B S hS O)).symm x)) =
      ((BigFppfOver.toScheme B S hS).map (Space.openSubHom (baseSiteObject B S hS) O)) x := by
  simp only [terminalPointsHomeomorph, Homeomorph.trans_apply,
    Space.pointsHomeomorphOfIso_apply, Iso.symm_hom, openToTerminal]
  rw [← Space.pointsMap_comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Space.schemePointsHomeomorph_symm_naturality, Homeomorph.apply_symm_apply]

/-- The points of `O ⊆ S`, read in the point space of the terminal presheaf, are the inverse
image of `O`. -/
theorem range_pointsMap_openToTerminal (O : S.Opens) :
    Set.range (Space.pointsMap B S hS _ (openToTerminal (B := B) (hS := hS) O)) =
      terminalPointsHomeomorph B S hS ⁻¹' (O : Set S) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Space.schemePointsHomeomorph B S hS (openSiteObject B S hS O)).symm.surjective q
    show terminalPointsHomeomorph B S hS _ ∈ (O : Set S)
    rw [terminalPointsHomeomorph_pointsMap_openToTerminal, Space.toScheme_map_openSubHom]
    exact x.2
  · intro hp
    let x : (BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS O) :=
      ⟨terminalPointsHomeomorph B S hS p, hp⟩
    refine ⟨(Space.schemePointsHomeomorph B S hS (openSiteObject B S hS O)).symm x, ?_⟩
    apply (terminalPointsHomeomorph B S hS).injective
    rw [terminalPointsHomeomorph_pointsMap_openToTerminal, Space.toScheme_map_openSubHom]
    rfl

/-! ### The counterexample -/

variable (B S hS) in
/-- The complement of `O`, as a closed subset of the point space of the terminal presheaf. -/
noncomputable abbrev complPoints (O : S.Opens) :
    Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) :=
  terminalPointsHomeomorph B S hS ⁻¹' (O : Set S)ᶜ

/-- The complement of `O` is closed in the point space of the terminal presheaf. -/
theorem isClosed_complPoints (O : S.Opens) : IsClosed (complPoints B S hS O) :=
  O.isOpen.isClosed_compl.preimage (terminalPointsHomeomorph B S hS).continuous

/-- The complement of `complPoints B S hS O` is the image of the points of `O ⊆ S`. -/
theorem compl_complPoints (O : S.Opens) :
    (complPoints B S hS O)ᶜ =
      Set.range (Space.pointsMap B S hS _ (openToTerminal (B := B) (hS := hS) O)) := by
  rw [range_pointsMap_openToTerminal, complPoints, Set.preimage_compl, compl_compl]

/-- The identity of the completion of `O ⊆ S` along the empty set is a formal modification. -/
theorem isFormalModification_id_completionSheaf_openSiteObject (hSN : IsLocallyNoetherian S)
    (O : S.Opens) :
    FormalSpace.IsFormalModification B S hS
      (𝟙 (Space.completionSheaf B S hS (yoneda.obj (openSiteObject B S hS O)) ∅)) := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS O)) :=
    inferInstanceAs (IsLocallyNoetherian (O : Scheme.{u}))
  have hN : Space.IsLocallyNoetherian B S hS (yoneda.obj (openSiteObject B S hS O)) :=
    Space.isLocallyNoetherian_yoneda B S hS _ inferInstance
  have h := FormalSpace.isFormalModification_completionSheafMap
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hN (𝟙 _) ∅
    isClosed_empty (Space.isProper_of_isIso B S hS _) inferInstance
  have e : Space.completionSheafMap B S hS (𝟙 (yoneda.obj (openSiteObject B S hS O))) ∅ =
      𝟙 (Space.completionSheaf B S hS (yoneda.obj (openSiteObject B S hS O)) ∅) :=
    (Space.completionSheafRestrict_self B S hS _ _ le_rfl).symm.trans
      (Space.completionSheafRestrict_id B S hS _ _)
  rwa [e] at h

/-- The inclusion of an open subscheme `O ⊆ S` is locally of finite type. -/
theorem locallyOfFiniteType_openSubHom (O : S.Opens) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (Space.openSubHom (baseSiteObject B S hS) O)) := by
  rw [Space.toScheme_map_openSubHom]
  exact inferInstanceAs (LocallyOfFiniteType (O.ι : (O : Scheme.{u}) ⟶ S))

/-- The structure morphism `O → S` of an open subscheme is locally of finite type. -/
theorem locallyOfFiniteType_terminal_from_openSiteObject (O : S.Opens) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (terminal.from (openSiteObject B S hS O))) := by
  have e : terminal.from (openSiteObject B S hS O) = Space.openSubHom (baseSiteObject B S hS) O ≫
      (((Over.mkIdTerminal (X := B.obj hS))).uniqueUpToIso terminalIsTerminal).hom :=
    terminal.hom_ext _ _
  rw [e, Functor.map_comp]
  have := locallyOfFiniteType_openSubHom (B := B) (hS := hS) O
  infer_instance

variable (B S hS) in
/-- **The situation of the counterexample to Stacks 0GHE without properness.** Over a locally
Noetherian scheme `S` with an open subscheme `O`: `X' = O`, `T' = ∅`, `W = X'_{/T'}` and
`g = id`. -/
noncomputable def openSituation (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    ContractionSituation B S hS :=
  have hmod := isFormalModification_id_completionSheaf_openSiteObject (B := B) (hS := hS) hSN O
  have hred := FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace B S hS _
    hmod.isLocallyNoetherian_target.1
  { isLocallyNoetherian_base := hSN
    X' := yoneda.obj (openSiteObject B S hS O)
    isAlgebraicSpace_X' := isAlgebraicSpace_yoneda B S hS _
    isLocallyOfFiniteType_X' :=
      Space.holdsOnEveryEtaleChart_of_isTerminal B S hS
        (Space.isTerminal_yoneda_obj_terminal B S hS) terminalIsTerminal
        (yoneda.map (terminal.from (openSiteObject B S hS O))) _
        ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS _).2
          (locallyOfFiniteType_terminal_from_openSiteObject O))
    T' := ∅
    isClosed_T' := isClosed_empty
    W := Space.completionSheaf B S hS (yoneda.obj (openSiteObject B S hS O)) ∅
    isLocallyNoetherian_W := hmod.isLocallyNoetherian_target
    Wred := hred.choose
    WredInclusion := hred.choose_spec.choose
    isReduction_WredInclusion := hred.choose_spec.choose_spec
    isLocallyOfFiniteType_Wred :=
      isLocallyOfFiniteTypeULift_of_isReduction_completionSheaf _
        (locallyOfFiniteType_terminal_from_openSiteObject O) ∅
        isClosed_empty _ _ hred.choose_spec.choose_spec
    g := 𝟙 _
    isFormalModification_g := hmod }

/-- The structure morphism of `O ⊆ S` to the terminal presheaf is `openToTerminal`. -/
private theorem terminal_from_yoneda_openSiteObject (O : S.Opens) :
    terminal.from (yoneda.obj (openSiteObject B S hS O)) = openToTerminal O :=
  terminal.hom_ext _ _

/-- Hypothesis (1) of Stacks 0GHE for the counterexample: the inverse image of `Z = S ∖ O` in
`X' = O` is empty. -/
theorem openSituation_preimage (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    Space.pointsMap B S hS (openSituation B S hS hSN O).X'
      (terminal.from (openSituation B S hS hSN O).X') ⁻¹' complPoints B S hS O =
      (openSituation B S hS hSN O).T' := by
  show Space.pointsMap B S hS (yoneda.obj (openSiteObject B S hS O))
    (terminal.from (yoneda.obj (openSiteObject B S hS O))) ⁻¹' complPoints B S hS O = ∅
  rw [terminal_from_yoneda_openSiteObject]
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hx' : Space.pointsMap B S hS _ (openToTerminal O) x ∈ (complPoints B S hS O)ᶜ := by
    rw [compl_complPoints]
    exact ⟨x, rfl⟩
  exact hx' hx

/-- Every point of `O` maps into the complement of `complPoints B S hS O`. -/
theorem compl_empty_subset_preimage_compl_complPoints (O : S.Opens) :
    (∅ : Set (Space.points B S hS (yoneda.obj (openSiteObject B S hS O))))ᶜ ⊆
      Space.pointsMap B S hS _ (openToTerminal O) ⁻¹' (complPoints B S hS O)ᶜ := by
  intro x _
  rw [Set.mem_preimage, compl_complPoints]
  exact ⟨x, rfl⟩

/-- The morphism `U' = O ⟶ S ∖ Z = O` of hypothesis (2) for the counterexample. -/
noncomputable def openSituationU (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    (openSituation B S hS hSN O).U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
        (complPoints B S hS O)ᶜ).toFunctor :=
  Space.openSubspaceOfPointsRestrict B S hS (openToTerminal O) _ _
    (compl_empty_subset_preimage_compl_complPoints O)

/-- The morphism `openSituationU` from `U' = O` to `S ∖ Z = O` is an isomorphism. -/
instance isIso_openSituationU (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    IsIso (openSituationU (B := B) (hS := hS) hSN O) := by
  have hk := isOpenImmersion_openToTerminal (B := B) (hS := hS) O
  have hmono : Mono (openToTerminal (B := B) (hS := hS) O) :=
    Space.mono_of_isOpenImmersion B S hS _ hk
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
  rw [isIso_iff_bijective]
  have hinj : Function.Injective ((openToTerminal (B := B) (hS := hS) O).app V) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono V)
  refine ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), fun y => ?_⟩
  have hy : y.1 ∈ (Subfunctor.range (openToTerminal (B := B) (hS := hS) O)).obj V := by
    rw [Space.range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS _ hk,
      ← compl_complPoints]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨⟨x, fun z _ => Set.notMem_empty z⟩, Subtype.ext hx⟩

/-- Hypothesis (2) of Stacks 0GHE for the counterexample: `U' → S ∖ Z` is an isomorphism, so a
closed immersion. -/
theorem isClosedImmersion_openSituationU (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    Space.IsClosedImmersion B S hS (openSituationU (B := B) (hS := hS) hSN O) :=
  Space.isClosedImmersion_of_isIso B S hS _

/-- `∅ ⟶ O` induces an isomorphism of the completion subfunctors along the empty set. -/
instance isIso_completionSubfunctorRestrict_emptyToOpen (O : S.Opens) :
    IsIso (Space.completionSubfunctorRestrict B S hS
      (yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (openSiteObject B S hS O)))
        ∅ ∅ (Set.empty_subset _)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
  rw [isIso_iff_bijective]
  refine ⟨fun x y _ => ?_, fun y => ?_⟩
  · have := isEmpty_toScheme_of_hom_emptySiteObject x.1.down
    exact Subtype.ext (ULift.ext (hom_ext_of_isEmpty _ _))
  · have := isEmpty_toScheme_of_hasImageIn_empty y.2
    exact ⟨⟨ULift.up (homOfIsEmpty _ _), hasImageIn_empty_of_isEmpty _⟩,
      Subtype.ext (ULift.ext (hom_ext_of_isEmpty _ _))⟩

/-- `∅ ⟶ O` induces an isomorphism of the completion sheaves along the empty set. -/
instance isIso_completionSheafRestrict_emptyToOpen (O : S.Opens) :
    IsIso (Space.completionSheafRestrict B S hS
      (yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (openSiteObject B S hS O)))
        ∅ ∅ (Set.empty_subset _)) :=
  Functor.map_isIso _ _

/-- Any morphism of completions out of a completion of the empty scheme into a completion of
`S` is a closed immersion: it is the completion of the closed immersion `∅ → S`. -/
theorem isClosedImmersion_completionSheafRestrict_emptySiteObject
    (m : yoneda.obj (emptySiteObject B S hS) ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (T₀ : Set (Space.points B S hS (yoneda.obj (emptySiteObject B S hS))))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (h : T₀ ⊆ Space.pointsMap B S hS _ m ⁻¹' Z) :
    FormalSpace.IsClosedImmersion B S hS (Space.completionSheafRestrict B S hS m T₀ Z h) := by
  obtain rfl : T₀ = Space.pointsMap B S hS _ m ⁻¹' Z :=
    Set.ext fun x => isEmptyElim x
  rw [Space.completionSheafRestrict_self]
  have hm : m = yoneda.map emptyToBase ≫ (baseYonedaIso B S hS).hom := terminal.hom_ext _ _
  refine FormalSpace.isClosedImmersion_completionSheafMap B S hS
    (isAlgebraicSpace_yoneda B S hS _) (Space.isAlgebraicSpace_terminal B S hS) m Z ?_
  rw [hm]
  refine Space.isClosedImmersion_comp B S hS _ _ ?_ (Space.isClosedImmersion_of_isIso B S hS _)
  exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).2 inferInstance

/-- The morphism `W = X'_{/∅} ⟶ S_{/Z}` of hypothesis (3) for the counterexample. -/
noncomputable def openSituationW (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    (openSituation B S hS hSN O).W ⟶
      Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (complPoints B S hS O) :=
  Space.completionSheafRestrict B S hS (openToTerminal O) ∅ _ (Set.empty_subset _)

/-- Hypothesis (3) of Stacks 0GHE for the counterexample: `W → S_{/Z}` is a closed immersion,
`W` being empty. -/
theorem isClosedImmersion_openSituationW (hSN : IsLocallyNoetherian S) (O : S.Opens) :
    FormalSpace.IsClosedImmersion B S hS (openSituationW (B := B) (hS := hS) hSN O) := by
  have hcomp := Space.completionSheafRestrict_comp B S hS
    (yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (openSiteObject B S hS O)))
    (openToTerminal O) ∅ ∅ (complPoints B S hS O) (Set.empty_subset _) (Set.empty_subset _)
    (Set.empty_subset _)
  have e := (IsIso.inv_comp_eq _).2 hcomp
  have key := FormalSpace.isClosedImmersion_comp B S hS _ _
    (FormalSpace.isClosedImmersion_of_isIso B S hS (inv (Space.completionSheafRestrict B S hS
      (yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (openSiteObject B S hS O)))
        ∅ ∅ (Set.empty_subset _))))
    (isClosedImmersion_completionSheafRestrict_emptySiteObject
      (yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (openSiteObject B S hS O)) ≫
        openToTerminal O) ∅ (complPoints B S hS O) (Set.empty_subset _))
  rwa [e] at key

/-- **The counterexample has no solution with `X → S` a closed immersion**, as soon as `O` is
not closed: such a solution would make `X' = O → S` proper, so its image `O` closed. -/
theorem not_exists_solution_openSituation (hSN : IsLocallyNoetherian S) (O : S.Opens)
    (hO : ¬ IsClosed (O : Set S)) :
    ¬ ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : (openSituation B S hS hSN O).Solution X),
      Space.IsClosedImmersion B S hS (terminal.from X) := by
  rintro ⟨X, s, hX⟩
  have h := isClosed_range_pointsMap_terminal_from_X'_of_solution _ s hX
  change IsClosed (Set.range (Space.pointsMap B S hS _
    (terminal.from (yoneda.obj (openSiteObject B S hS O))))) at h
  rw [terminal_from_yoneda_openSiteObject, range_pointsMap_openToTerminal] at h
  apply hO
  have := h.preimage (terminalPointsHomeomorph B S hS).symm.continuous
  rwa [← Homeomorph.image_eq_preimage_symm, Homeomorph.image_preimage] at this

/-! ### The statement decided -/

/-- **Stacks 0GHE, decided.** In the situation of Stacks 0GH8, over a locally Noetherian scheme
`S`:

1. if `X' → S` is proper and `Z ⊆ |S|` is a closed subset such that the inverse image of `Z` in
   `X'` is `T'`, the morphism `u : U' → S ∖ Z` is a closed immersion and the morphism
   `w : W → S_{/Z}` is a closed immersion, then there exists a solution `(f : X' → X, T, a)`, and
   moreover `X → S` is a closed immersion (the solution produced also has `|U| = |X| ∖ T`); and
2. without the hypothesis that `X' → S` is proper, the statement fails as soon as `S` has a
   closed subset which is not open (for instance `S = 𝔸¹_k`, with the closed point `0`): for an
   open `O ⊆ S` which is not closed, the situation `(X' = O, T' = ∅, W = X'_{/T'}, g = id)` with
   `Z = S ∖ O` satisfies the three conditions, but has no solution with `X → S` a closed
   immersion, since such a solution would make `X' → S` proper and hence `O` closed in `S`.

Part 1 is `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isClosedImmersion`;
part 2 is `AlgebraicGeometry.Artin.ContractionSituation.not_exists_solution_openSituation`. -/
@[stacks 0GHE "erratum: as printed online the lemma is false without the hypothesis that \
X' → S is proper (part 2, over any S with a closed subset that is not open, e.g. S = 𝔸¹_k, \
Z = {0}, X' = 𝔾_m, T' = ∅); with that hypothesis, which the source's proof uses, it holds (part 1)"]
theorem exists_solution_of_isClosedImmersion_and_not_forall (hSN : IsLocallyNoetherian S) :
    (∀ (c : ContractionSituation B S hS), Space.IsProper B S hS (terminal.from c.X') →
      ∀ (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))), IsClosed Z →
      Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T' →
      ∀ (u : c.U'.toFunctor ⟶
        (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor),
        Space.IsClosedImmersion B S hS u →
      ∀ (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z),
        FormalSpace.IsClosedImmersion B S hS w →
      ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : c.Solution X),
        Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        Space.IsClosedImmersion B S hS (terminal.from X)) ∧
    ((∃ Z : Set S, IsClosed Z ∧ ¬ IsOpen Z) →
      ¬ ∀ (c : ContractionSituation B S hS)
        (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))), IsClosed Z →
        Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T' →
        ∀ (u : c.U'.toFunctor ⟶
          (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor),
          Space.IsClosedImmersion B S hS u →
        ∀ (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z),
          FormalSpace.IsClosedImmersion B S hS w →
        ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : c.Solution X),
          Space.IsClosedImmersion B S hS (terminal.from X)) := by
  refine ⟨exists_solution_of_isClosedImmersion, ?_⟩
  rintro ⟨Z, hZ, hZo⟩ h
  let O : S.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  exact not_exists_solution_openSituation hSN O (by simpa [O] using hZo)
    (h (openSituation B S hS hSN O) (complPoints B S hS O) (isClosed_complPoints O)
      (openSituation_preimage hSN O) (openSituationU hSN O) (isClosedImmersion_openSituationU hSN O)
      (openSituationW hSN O) (isClosedImmersion_openSituationW hSN O))

end AlgebraicGeometry.Artin.ContractionSituation

end

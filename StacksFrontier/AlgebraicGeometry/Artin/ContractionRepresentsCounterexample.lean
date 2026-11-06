module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLocus
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionReductionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Stacks 0GHB is false as printed

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
**Stacks 0GHB** reads

> if there exists a solution `(f : X' → X, T, a)` then there is a functorial bijection
> `F(V) = Mor_S(V, X)` on the category of locally Noetherian schemes `V` over `S`.

A solution is defined in the prose after Situation 0GH8, and condition (2) of that definition
only asks that `f` map `U'` isomorphically onto *some* open subspace `U ⊆ X`; it does not ask
that `|U| = |X| ∖ T`. The library's `AlgebraicGeometry.Artin.ContractionSituation.Solution`
follows the definition literally. With that definition the lemma fails, because nothing ties
the part of `X` away from `T` and from `U` to the data `(X', T', W, g)` which `F` sees.

The smallest counterexample takes `X'` empty. Let `S` be a nonempty locally Noetherian scheme,
`X' = ∅`, `T' = ∅`, `W = X'_{/T'}` and `g = id`
(`AlgebraicGeometry.Artin.ContractionSituation.emptySituation`). Then
* `X = X'` with `f = id`, `T = ∅`, `U = U'` and `a = id` is a solution
  (`AlgebraicGeometry.Artin.ContractionSituation.emptySituationSolutionSelf`), and
* `X = S` with `f : ∅ → S`, `T = ∅`, `U = ∅` and `a = f_{/T}⁻¹` is a solution too
  (`AlgebraicGeometry.Artin.ContractionSituation.emptySituationSolutionBase`): `f` is a closed
  immersion, hence proper; `T' = f⁻¹T`; `f` maps `U' = ∅` isomorphically onto the open subspace
  `U = ∅`; and both completions along the empty set are the empty formal space.

If 0GHB held for both, `Mor_S(-, ∅)` and `Mor_S(-, S)` would be isomorphic functors on locally
Noetherian schemes over `S`; at `V = S` the second has an element and the first has none.
This is `AlgebraicGeometry.Artin.ContractionSituation.not_forall_nonempty_iso_of_solution`.
(Directly: `F(V)` is empty for every nonempty `V`, since `u' : V ∖ Z → U' = ∅` forces `Z = V`
and `x̂ : V_{/V} → W = ∅` is then impossible; so the solution `X = S` is not represented.)

The proof of 0GHB in the source uses `u' : V ∖ Z → U' = U` as the restriction of `x` to
`V ∖ Z = x⁻¹(|X| ∖ T)`, that is, it reads `U` as the open subspace with `|U| = |X| ∖ T`. The
corrected statement, with that extra condition, is in
`StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresents`.

## Main definitions

* `emptySiteObject`: the empty scheme as an object of the big fppf site over `S`.
* `emptySituation`: the situation `(X' = ∅, T' = ∅, W = X'_{/T'}, g = id)` of Stacks 0GH8.
* `emptySituationSolutionSelf` and `emptySituationSolutionBase`: two solutions of it, with
  targets `∅` and `S`.

## Main results

* `not_forall_nonempty_iso_of_solution`: the statement of Stacks 0GHB, for the literal notion of
  solution, fails over every nonempty locally Noetherian scheme `S`.
* `isLocallyOfFiniteTypeULift_of_isReduction_completionSheaf`: the reduction of the completion
  of a scheme locally of finite type over `S` along a closed subset is locally of finite type over
  `S`.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Objects of the site with empty underlying scheme -/

variable (B S hS) in
/-- The empty scheme, as an object of the big fppf site over `S`. -/
noncomputable abbrev emptySiteObject : BigFppfOver B S hS :=
  siteObject B S hS (B.contains_of_mono (Scheme.emptyTo S) hS) (Scheme.emptyTo S)

/-- The underlying scheme of `emptySiteObject` is empty. -/
instance isEmpty_toScheme_emptySiteObject :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj (emptySiteObject B S hS)) :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

/-- Two morphisms of the site out of an object whose underlying scheme is empty are equal. -/
theorem hom_ext_of_isEmpty {V W : BigFppfOver B S hS}
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj V)] (a b : V ⟶ W) : a = b :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj V)).hom_ext _ _)

/-- The morphism of the site out of an object whose underlying scheme is empty. -/
noncomputable def homOfIsEmpty (V W : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj V)] : V ⟶ W :=
  Over.homMk (ObjectProperty.homMk
      ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj V)).to _))
    (by
      apply ObjectProperty.hom_ext
      exact (isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj V)).hom_ext _ _)

/-- An object of the site with a morphism to the empty scheme has empty underlying scheme. -/
theorem isEmpty_toScheme_of_hom_emptySiteObject {V : BigFppfOver B S hS}
    (x : V ⟶ emptySiteObject B S hS) : IsEmpty ((BigFppfOver.toScheme B S hS).obj V) :=
  ⟨fun v => isEmptyElim (α := (BigFppfOver.toScheme B S hS).obj (emptySiteObject B S hS))
    (((BigFppfOver.toScheme B S hS).map x).base v)⟩

/-- An object of the site whose space of points is empty has empty underlying scheme. -/
theorem isEmpty_toScheme_of_isEmpty_points {V : BigFppfOver B S hS}
    (h : IsEmpty (Space.points B S hS (yoneda.obj V))) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) :=
  (Space.pointsEquivScheme B S hS V).symm.isEmpty

/-- An object of the site carrying a section of a presheaf whose point-set image is empty has
empty underlying scheme. -/
theorem isEmpty_toScheme_of_mem_openSubspaceOfPoints_empty
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} {x : F.obj (op V)}
    (hx : x ∈ (Space.openSubspaceOfPoints B S hS F ∅).obj (op V)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) :=
  isEmpty_toScheme_of_isEmpty_points ⟨fun p => Set.notMem_empty _ (hx ⟨p, rfl⟩)⟩

/-- An object of the site carrying a section of a presheaf which has image in the empty set,
in the sense of the completion of Stacks 0AMC, has empty underlying scheme: it has no
field-valued points. -/
theorem isEmpty_toScheme_of_hasImageIn_empty
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} {x : F.obj (op V)}
    (hx : Space.HasImageIn B S hS F ∅ V x) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨p, -⟩ := Quot.exists_rep ((Space.pointsEquivScheme B S hS V).symm v)
  exact Set.notMem_empty _ (hx p)

/-- Every section of a presheaf over an object of the site with empty underlying scheme has
image in the empty set, in the sense of the completion of Stacks 0AMC. -/
theorem hasImageIn_empty_of_isEmpty {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} [IsEmpty ((BigFppfOver.toScheme B S hS).obj V)] (x : F.obj (op V)) :
    Space.HasImageIn B S hS F ∅ V x := fun p =>
  isEmptyElim (Space.pointsEquivScheme B S hS V
    (Space.FieldValuedPoint.class B S hS (yoneda.obj V) p))

/-! ### The reduction of the completion of a scheme -/

/-- The universe-lifted Yoneda presheaf of the terminal object of the site is terminal. -/
noncomputable def isTerminalULiftYonedaObjTerminal :
    IsTerminal ((uliftYoneda.{u + 1}).obj (⊤_ (BigFppfOver B S hS))) :=
  terminalIsTerminal.isTerminalObj uliftYoneda.{u + 1} _

/-- **The reduction of the completion of a scheme locally of finite type is locally of finite
type.** For an object `Y` of the site locally of finite type over `S` and a closed subset
`T ⊆ |Y|`, every reduction of the completion `Y_{/T}` is locally of finite type over `S`: it
is a reduced algebraic space with a representable closed immersion into `Y_{/T}`, so its
morphism to `Y` is representable and locally of finite type
(`AlgebraicGeometry.FormalSpace.relative_locallyOfFiniteType_comp_completionSheafToAmbient`). -/
theorem isLocallyOfFiniteTypeULift_of_isReduction_completionSheaf (Y : BigFppfOver B S hS)
    (hY : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (terminal.from Y)))
    (T : Set (Space.points B S hS (yoneda.obj Y))) (hT : IsClosed T)
    (Wred : FormalSpace.FppfSheaf B S hS)
    (i : Wred ⟶ Space.completionSheaf B S hS (yoneda.obj Y) T)
    (hi : FormalSpace.IsReduction B S hS _ Wred i) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj) := by
  let L := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let CI := MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : L.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have : MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun X => (inferInstance : _root_.AlgebraicGeometry.LocallyOfFiniteType (𝟙 X))⟩
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.mk _ (fun _ _ hf => by have := hf; infer_instance)
      (fun _ _ hf => by have := hf; infer_instance)
  have : L.ContainsIdentities := MorphismProperty.ContainsIdentities.inverseImage _
  have : L.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have : (L.relative uliftYoneda.{u + 1}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition L
  have hTh : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ CI := fun _ _ _ hm ↦ hm.1
  have hiCI : CI.relative uliftYoneda.{u + 1} i.hom :=
    MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1}) hTh _
      hi.isRepresentableThickening
  have hid : L.relative uliftYoneda.{u + 1}
      (𝟙 (Space.completionSheaf B S hS (yoneda.obj Y) T).obj) :=
    MorphismProperty.relative.of_exists
      (fun Y' g ↦ ⟨Y', g, 𝟙 Y', by simpa using IsPullback.of_id_snd, L.id_mem _⟩)
  have key := FormalSpace.relative_locallyOfFiniteType_comp_completionSheafToAmbient B S hS
    (isAlgebraicSpace_yoneda B S hS Y) T hT (𝟙 _) hid i hi.algebraic hi.reduced hiCI
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS (@LocallyOfFiniteType.{u})
  have hmap : L.relative uliftYoneda.{u + 1} ((uliftYoneda.{u + 1}).map (terminal.from Y)) :=
    MorphismProperty.relative_map (P := L) hY
  have h1 := Space.isLocallyOfFiniteTypeULift_of_relative B S hS _
    (MorphismProperty.comp_mem _ _ _ key hmap)
  have h2 := Space.holdsOnEveryEtaleChartULift_postcomp B S hS _
    (isTerminalULiftYonedaObjTerminal.uniqueUpToIso terminalIsTerminal).hom _ h1
  convert h2 using 2
  exact terminal.hom_ext _ _

/-! ### The situation with empty `X'` -/

/-- The completion of the empty scheme along the empty set: the identity of it is a formal
modification, by Stacks 0GDM for the identity of the empty scheme. -/
theorem isFormalModification_id_completionSheaf_emptySiteObject :
    FormalSpace.IsFormalModification B S hS
      (𝟙 (Space.completionSheaf B S hS (yoneda.obj (emptySiteObject B S hS)) ∅)) := by
  have hN : Space.IsLocallyNoetherian B S hS (yoneda.obj (emptySiteObject B S hS)) :=
    Space.isLocallyNoetherian_yoneda B S hS _ inferInstance
  have h := FormalSpace.isFormalModification_completionSheafMap
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hN (𝟙 _) ∅
    isClosed_empty (Space.isProper_of_isIso B S hS _) inferInstance
  have e : Space.completionSheafMap B S hS (𝟙 (yoneda.obj (emptySiteObject B S hS))) ∅ =
      𝟙 (Space.completionSheaf B S hS (yoneda.obj (emptySiteObject B S hS)) ∅) :=
    (Space.completionSheafRestrict_self B S hS _ _ le_rfl).symm.trans
      (Space.completionSheafRestrict_id B S hS _ _)
  rwa [e] at h

variable (B S hS) in
/-- **The situation of the counterexample to Stacks 0GHB.** Over a locally Noetherian scheme
`S`: the empty algebraic space `X' = ∅`, the closed subset `T' = ∅`, the formal algebraic space
`W = X'_{/T'}` and the formal modification `g = id`. -/
noncomputable def emptySituation (hSN : IsLocallyNoetherian S) :
    ContractionSituation B S hS :=
  have hmod := isFormalModification_id_completionSheaf_emptySiteObject (B := B) (hS := hS)
  have hred := FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace B S hS _
    hmod.isLocallyNoetherian_target.1
  { isLocallyNoetherian_base := hSN
    X' := yoneda.obj (emptySiteObject B S hS)
    isAlgebraicSpace_X' := isAlgebraicSpace_yoneda B S hS _
    isLocallyOfFiniteType_X' :=
      Space.holdsOnEveryEtaleChart_of_isTerminal B S hS
        (Space.isTerminal_yoneda_obj_terminal B S hS) terminalIsTerminal
        (yoneda.map (terminal.from (emptySiteObject B S hS))) _
        ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS _).2 inferInstance)
    T' := ∅
    isClosed_T' := isClosed_empty
    W := Space.completionSheaf B S hS (yoneda.obj (emptySiteObject B S hS)) ∅
    isLocallyNoetherian_W := hmod.isLocallyNoetherian_target
    Wred := hred.choose
    WredInclusion := hred.choose_spec.choose
    isReduction_WredInclusion := hred.choose_spec.choose_spec
    isLocallyOfFiniteType_Wred :=
      isLocallyOfFiniteTypeULift_of_isReduction_completionSheaf _ inferInstance ∅
        isClosed_empty _ _ hred.choose_spec.choose_spec
    g := 𝟙 _
    isFormalModification_g := hmod }

/-- **The first solution: `X = X' = ∅`.** The identity of `X'`, the empty closed subset, the
open subspace `U = U'` and the identity of `W`. -/
noncomputable def emptySituationSolutionSelf (hSN : IsLocallyNoetherian S) :
    Solution (emptySituation B S hS hSN) (yoneda.obj (emptySiteObject B S hS)) where
  isAlgebraicSpace_X := isAlgebraicSpace_yoneda B S hS _
  f := 𝟙 (yoneda.obj (emptySiteObject B S hS))
  isProper_f := Space.isProper_of_isIso B S hS (𝟙 (yoneda.obj (emptySiteObject B S hS)))
  T := ∅
  isClosed_T := isClosed_empty
  preimage_T := Set.preimage_empty
  U := (emptySituation B S hS hSN).U'
  isOpenSubspace_U := (emptySituation B S hS hSN).isOpenSubspace_U'
  isoU := Iso.refl _
  isoU_comp_ι := (Category.id_comp _).trans (Category.comp_id _).symm
  a := Iso.refl _
  completion_comp_a := (Category.comp_id _).trans (Space.completionSheafRestrict_id B S hS _ _)

variable (B S hS) in
/-- The scheme `S` itself, as an object of the big fppf site over `S`. -/
noncomputable abbrev baseSiteObject : BigFppfOver B S hS :=
  siteObject B S hS hS (𝟙 S)

/-- The morphism `∅ ⟶ S` of the site. -/
noncomputable abbrev emptyToBase : emptySiteObject B S hS ⟶ baseSiteObject B S hS :=
  homOfIsEmpty _ _

/-- The points of the empty scheme: there are none. -/
instance isEmpty_points_yoneda_emptySiteObject :
    IsEmpty (Space.points B S hS (yoneda.obj (emptySiteObject B S hS))) :=
  (Space.pointsEquivScheme B S hS _).isEmpty

/-- `∅ ⟶ S` maps every point into the empty set. -/
theorem compl_empty_subset_preimage_empty :
    (∅ : Set (Space.points B S hS (yoneda.obj (emptySiteObject B S hS))))ᶜ ⊆
      Space.pointsMap B S hS _ (yoneda.map (emptyToBase (B := B) (hS := hS))) ⁻¹' ∅ :=
  fun p _ => isEmptyElim p

/-- `∅ ⟶ S` maps `U' = X'` isomorphically onto the open subspace of `S` with no points: over an
object `V` of the site both sides are empty unless `V` is the empty scheme, and then both are a
point. -/
instance isIso_openSubspaceOfPointsRestrict_emptyToBase :
    IsIso (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (emptyToBase (B := B) (hS := hS)))
      _ _ compl_empty_subset_preimage_empty) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
  rw [isIso_iff_bijective]
  refine ⟨fun x y _ => ?_, fun y => ?_⟩
  · have := isEmpty_toScheme_of_hom_emptySiteObject x.1
    exact Subtype.ext (hom_ext_of_isEmpty _ _)
  · have := isEmpty_toScheme_of_mem_openSubspaceOfPoints_empty y.2
    exact ⟨⟨homOfIsEmpty _ _, fun _ _ => Set.notMem_empty _⟩,
      Subtype.ext (hom_ext_of_isEmpty _ _)⟩

/-- `∅ ⟶ S` induces an isomorphism of the subfunctors whose sheafifications are the completions
along the empty set: over an object `V` of the site both sides are empty unless `V` is the empty
scheme, and then both are a point. -/
instance isIso_completionSubfunctorRestrict_emptyToBase :
    IsIso (Space.completionSubfunctorRestrict B S hS
      (yoneda.map (emptyToBase (B := B) (hS := hS))) ∅ ∅ (Set.empty_subset _)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
  rw [isIso_iff_bijective]
  refine ⟨fun x y _ => ?_, fun y => ?_⟩
  · have := isEmpty_toScheme_of_hom_emptySiteObject x.1.down
    exact Subtype.ext (ULift.ext (hom_ext_of_isEmpty _ _))
  · have := isEmpty_toScheme_of_hasImageIn_empty y.2
    exact ⟨⟨ULift.up (homOfIsEmpty _ _), hasImageIn_empty_of_isEmpty _⟩,
      Subtype.ext (ULift.ext (hom_ext_of_isEmpty _ _))⟩

/-- `∅ ⟶ S` induces an isomorphism of the completions along the empty set. -/
instance isIso_completionSheafRestrict_emptyToBase :
    IsIso (Space.completionSheafRestrict B S hS
      (yoneda.map (emptyToBase (B := B) (hS := hS))) ∅ ∅ (Set.empty_subset _)) :=
  Functor.map_isIso _ _

/-- The isomorphism `U' ≅ U` of the second solution: `∅ ⟶ S` restricted to `U' = X'`. -/
noncomputable def emptyIsoU :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj (emptySiteObject B S hS)) ∅ᶜ).toFunctor ≅
      (Space.openSubspaceOfPoints B S hS (yoneda.obj (baseSiteObject B S hS)) ∅).toFunctor :=
  asIso (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map emptyToBase) _ _
    compl_empty_subset_preimage_empty)

/-- The isomorphism of completions along the empty set induced by `∅ ⟶ S`. -/
noncomputable def emptyCompletionIso :
    Space.completionSheaf B S hS (yoneda.obj (emptySiteObject B S hS)) ∅ ≅
      Space.completionSheaf B S hS (yoneda.obj (baseSiteObject B S hS)) ∅ :=
  asIso (Space.completionSheafRestrict B S hS (yoneda.map emptyToBase) ∅ ∅ (Set.empty_subset _))

/-- **The second solution: `X = S`.** The morphism `f : ∅ ⟶ S` (a closed immersion, hence
proper), the empty closed subset `T = ∅` (so that `T' = f⁻¹T`), the open subspace `U ⊆ S` with
no points (onto which `f` maps `U' = ∅` isomorphically) and the inverse of the isomorphism
`f_{/T} : X'_{/T'} ⟶ S_{/T}` (so that `g = id = a ∘ f_{/T}`). Here `|U| = ∅ ≠ |S| ∖ T`. -/
noncomputable def emptySituationSolutionBase (hSN : IsLocallyNoetherian S) :
    Solution (emptySituation B S hS hSN) (yoneda.obj (baseSiteObject B S hS)) where
  isAlgebraicSpace_X := isAlgebraicSpace_yoneda B S hS _
  f := yoneda.map emptyToBase
  isProper_f := Space.isProper_yoneda_map B S hS _ inferInstance
  T := ∅
  isClosed_T := isClosed_empty
  preimage_T := Set.preimage_empty
  U := Space.openSubspaceOfPoints B S hS _ ∅
  isOpenSubspace_U := Space.isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_yoneda B S hS _) ∅ isOpen_empty
  isoU := emptyIsoU
  isoU_comp_ι := rfl
  a := emptyCompletionIso.symm
  completion_comp_a := emptyCompletionIso.hom_inv_id

/-- **Stacks 0GHB is false as printed.** For the notion of solution of the prose after Situation
0GH8, read literally (`AlgebraicGeometry.Artin.ContractionSituation.Solution`: condition (2)
asks for *some* open subspace `U ⊆ X` onto which `f` maps `U'` isomorphically), it is not true
that every solution `X` carries a functorial bijection `F(V) = Mor_S(V, X)` on locally
Noetherian schemes `V` over `S`, as soon as `S` is a nonempty locally Noetherian scheme: the
situation `(X' = ∅, T' = ∅, W = X'_{/T'}, g = id)` has the two solutions `X = ∅` and `X = S`,
and `Mor_S(S, ∅)` is empty while `Mor_S(S, S)` is not. -/
theorem not_forall_nonempty_iso_of_solution (hSN : IsLocallyNoetherian S) [Nonempty S] :
    ¬ ∀ (c : ContractionSituation B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      Solution c X → Nonempty (contractionFunctor c ≅ morOnLocallyNoetherian B S hS X) := by
  intro h
  obtain ⟨α₁⟩ := h _ _ (emptySituationSolutionSelf hSN)
  obtain ⟨α₂⟩ := h _ _ (emptySituationSolutionBase hSN)
  let V : LocallyNoetherianOver B S hS := ⟨baseSiteObject B S hS, hSN⟩
  let e := (α₂.symm ≪≫ α₁).app (op V)
  let φ : baseSiteObject B S hS ⟶ emptySiteObject B S hS :=
    (e.hom (ULift.up (𝟙 (baseSiteObject B S hS)))).down
  obtain ⟨s⟩ := ‹Nonempty S›
  exact (isEmpty_toScheme_of_hom_emptySiteObject φ).false s

end AlgebraicGeometry.Artin.ContractionSituation

end

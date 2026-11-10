module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerRepresents
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresentsCounterexample
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Empty
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptySiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBaseInverse

/-!
# The final conclusion of Stacks 0GHD is false as printed

In the situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`), let `V` be a
locally Noetherian scheme over `S` and let `(Zᵢ, u'ᵢ, x̂ᵢ) ∈ F(V)`, `i = 1, 2`, with chosen
compatibility witnesses (`AlgebraicGeometry.Artin.ContractionEqualizer`). The last sentence of
**Stacks 0GHD** reads

> We conclude, using Lemmas 0GHB and 0GHC, that if there is a solution `E → V` for the triple in
> (4), then `E` represents `F ×_{Δ, F × F} V` on the category of locally Noetherian schemes over
> `V`.

A solution is defined in the prose after Situation 0GH8, and its condition (2) only asks that `f`
map `U'` isomorphically onto *some* open subspace `U` of `E`
(`AlgebraicGeometry.Artin.ContractionSituation.Solution` follows that definition literally). Read
that way the conclusion fails, for the same reason as Stacks 0GHB does: nothing ties the part of
`E` away from `U` and `T` to the triple of (4).

## The counterexample

Let `S` be a nonempty locally Noetherian scheme and `V = S`. Take `X' = S ⨿ S`, `T' = ∅`,
`W = X'_{/∅}` and `g = id` (`AlgebraicGeometry.Artin.ContractionSituation.doubleBaseSituation`),
and let the two triples of `F(V)` be those of the two inclusions `S ⟶ S ⨿ S`
(`AlgebraicGeometry.Artin.ContractionEqualizer.doubleBaseEqualizer`). The two inclusions agree
nowhere, so `E'` has no points; then `Z = ∅`, and `E'_{/Z}` and `E_W` are both the initial fppf
sheaf. Hence the triple of (4) is `(∅, ∅, ∅ → ∅)` over `V`, and *every* algebraic space over `V`
receiving a proper morphism from `∅` is a solution of it, with `T = ∅` and `U = ∅`
(`AlgebraicGeometry.Artin.ContractionSituation.solutionTerminalOfIsEmptyPoints`, applied to the
terminal object `E = V`). But `F ×_{Δ, F × F} V` has no element over `V` itself, as the two
inclusions differ, while `Mor_V(V, V)` contains the identity. So `E = V` does not represent
`F ×_{Δ, F × F} V`.

The source's proof of 0GHB, which 0GHD invokes, uses the open subspace `U` with `|U| = |E| ∖ T`;
for those solutions the conclusion holds
(`AlgebraicGeometry.Artin.ContractionEqualizer.morIsoDiagonalFibre`).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.solutionTerminalOfIsEmptyPoints`: for a situation
  whose algebraic space `X'` has no points and whose formal modification is an isomorphism, the
  final object of the site is a solution, with `T = ∅` and `U = ∅`.
* `AlgebraicGeometry.Artin.ContractionSituation.doubleBaseSituation`: the situation
  `(X' = S ⨿ S, T' = ∅, W = X'_{/∅}, g = id)` of Stacks 0GH8.
* `AlgebraicGeometry.Artin.ContractionEqualizer.doubleBaseEqualizer`: the data of Stacks 0GHD for
  the two inclusions `S ⟶ S ⨿ S`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.not_forall_nonempty_iso_diagonalFibre_of_solution`:
  the final conclusion of Stacks 0GHD, for the literal notion of solution, fails over every
  nonempty locally Noetherian scheme `S`.
* `AlgebraicGeometry.Space.isInitialCompletionSheafOfBotMem`: a completion whose completion
  subfunctor has sections only over objects covered by the empty sieve is the initial fppf sheaf.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Presheaves with no points -/

/-- A section of a presheaf with no points lives over an object covered by the empty sieve. -/
theorem bot_mem_of_isEmpty_points {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsEmpty (points B S hS F)) (U : (BigFppfOver B S hS)ᵒᵖ) (x : F.obj U) :
    (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop :=
  BigFppfOver.bot_mem_topology U.unop (isEmpty_of_isEmpty_points hF x)

/-- A presheaf all of whose sections live over objects with empty underlying scheme has no
points: a point is represented by a section over the spectrum of a field. -/
theorem isEmpty_points_of_forall_isEmpty {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ∀ A : BigFppfOver B S hS, F.obj (op A) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A)) :
    IsEmpty (points B S hS F) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, -⟩ := Quot.exists_rep x
  exact (h _ p.value).false (IsLocalRing.closedPoint p.carrier)

/-! ### Completions with no sections -/

variable (B S hS) in
/-- **A completion with no sections is initial.** If every section of the completion subfunctor
of `X` along `T` lives over an object covered by the empty sieve, then the completion `X_{/T}`
is an initial fppf sheaf: a morphism out of it is a morphism out of the completion subfunctor,
and an fppf sheaf has exactly one section over an object covered by the empty sieve. -/
noncomputable def isInitialCompletionSheafOfBotMem (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X))
    (hX : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (_ : (completionSubfunctor B S hS X T).toFunctor.obj U),
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    IsInitial (completionSheaf B S hS X T) :=
  let J := BigFppfOver.topology B S hS
  let η : ∀ G : Sheaf J (Type (u + 1)), (completionSubfunctor B S hS X T).toFunctor ⟶ G.obj :=
    fun G =>
      { app := fun U => ↾fun q => (nonempty_of_bot_mem B S hS G.property (hX U q)).some
        naturality := by
          intro U V f
          ext q
          exact (subsingleton_of_bot_mem B S hS G.property
            (hX V ((completionSubfunctor B S hS X T).toFunctor.map f q))).elim _ _ }
  IsInitial.ofUniqueHom (fun G => ObjectProperty.homMk (J.sheafifyLift (η G) G.property))
    (fun G m => ObjectProperty.hom_ext _ (J.sheafify_hom_ext _ _ G.property
      (hom_ext_of_bot_mem B S hS (fun _ hU => subsingleton_of_bot_mem B S hS G.property hU)
        hX _ _)))

variable (B S hS) in
/-- The completion of a presheaf along the empty set of points is the initial fppf sheaf: a
section with point-set image in the empty set lives over an object with empty underlying
scheme. -/
noncomputable def isInitialCompletionSheafEmpty (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsInitial (completionSheaf B S hS X ∅) :=
  isInitialCompletionSheafOfBotMem B S hS X ∅ fun U q =>
    BigFppfOver.bot_mem_topology U.unop
      (Artin.ContractionSituation.isEmpty_toScheme_of_hasImageIn_empty q.2)

end Space

namespace Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Solutions of a situation with no points -/

section IsEmptyPoints

variable (c : ContractionSituation B S hS)

/-- The morphism from an algebraic space `X'` with no points to the empty object of the site. -/
noncomputable def toEmptyOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X')) :
    c.X' ⟶ yoneda.obj (emptySiteObject B S hS) :=
  Space.toSheafOfBotMem B S hS (isAlgebraicSpace_yoneda B S hS _).isSheaf
    (Space.bot_mem_of_isEmpty_points hX)

/-- An algebraic space with no points is isomorphic to the empty object of the site. -/
theorem isIso_toEmptyOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X')) :
    IsIso (c.toEmptyOfIsEmptyPoints hX) :=
  ⟨⟨(Space.exists_hom_of_isEmpty (emptySiteObject B S hS) c.isAlgebraicSpace_X').some,
    Space.hom_ext_of_bot_mem B S hS
      (fun _ hU => Space.subsingleton_of_bot_mem B S hS c.isAlgebraicSpace_X'.isSheaf hU)
      (Space.bot_mem_of_isEmpty_points hX) _ _,
    Space.hom_ext_yoneda_of_isEmpty _ (isAlgebraicSpace_yoneda B S hS _) _ _⟩⟩

/-- The morphism from an algebraic space `X'` with no points to the final object of the site,
through the empty object. -/
noncomputable def toTerminalOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X')) :
    c.X' ⟶ yoneda.obj (BigFppfOver.terminalObj B S hS) :=
  c.toEmptyOfIsEmptyPoints hX ≫
    yoneda.map (homOfIsEmpty (emptySiteObject B S hS) (BigFppfOver.terminalObj B S hS))

/-- The morphism from an algebraic space with no points to the final object of the site is
proper: it is an isomorphism followed by the closed immersion of the empty scheme. -/
theorem isProper_toTerminalOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X')) :
    Space.IsProper B S hS (c.toTerminalOfIsEmptyPoints hX) :=
  have := c.isIso_toEmptyOfIsEmptyPoints hX
  Space.isProper_comp B S hS c.isAlgebraicSpace_X' (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) _ _ (Space.isProper_of_isIso B S hS _)
    (Space.isProper_yoneda_map B S hS _ inferInstance)

/-- When `X'` has no points, `U'` is isomorphic to the open subspace of the final object with no
points: both have exactly one section over each object covered by the empty sieve and none
elsewhere. -/
noncomputable def isoUOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X')) :
    c.U'.toFunctor ≅
      (Space.openSubspaceOfPoints B S hS (yoneda.obj (BigFppfOver.terminalObj B S hS))
        ∅).toFunctor where
  hom := Space.openSubspaceOfPointsRestrict B S hS (c.toTerminalOfIsEmptyPoints hX) c.T'ᶜ ∅
    (fun p _ => hX.elim p)
  inv := Space.homOfBotMem B S hS c.isAlgebraicSpace_X'.isSheaf c.T'ᶜ
    (fun _ y => Space.bot_mem_of_mem_openSubspaceOfPoints B S hS rfl y.2)
  hom_inv_id := Space.hom_ext_of_bot_mem B S hS (Q := c.U'.toFunctor) (G := c.U'.toFunctor)
    (fun _ hU => ⟨fun _ _ => Subtype.ext
      ((Space.subsingleton_of_bot_mem B S hS c.isAlgebraicSpace_X'.isSheaf hU).elim _ _)⟩)
    (fun U x => Space.bot_mem_of_isEmpty_points hX U x.1) _ _
  inv_hom_id := Space.hom_ext_of_bot_mem B S hS
    (Q := (Space.openSubspaceOfPoints B S hS (yoneda.obj (BigFppfOver.terminalObj B S hS))
      ∅).toFunctor)
    (G := (Space.openSubspaceOfPoints B S hS (yoneda.obj (BigFppfOver.terminalObj B S hS))
      ∅).toFunctor)
    (fun _ hU => ⟨fun _ _ => Subtype.ext ((Space.subsingleton_of_bot_mem B S hS
      (isAlgebraicSpace_yoneda B S hS _).isSheaf hU).elim _ _)⟩)
    (fun _ y => Space.bot_mem_of_mem_openSubspaceOfPoints B S hS rfl y.2) _ _

/-- **A situation with no points has the final object as a literal solution.** If the algebraic
space `X'` of a situation of Stacks 0GH8 has no points and its formal modification
`g : X'_{/T'} ⟶ W` is an isomorphism, then the final object `S` of the site is a solution in the
sense of the prose after Situation 0GH8: `f : X' ⟶ S` is proper (through `X' ≅ ∅`), `T = ∅`
pulls back to `T' = ∅`, `f` maps `U' = ∅` isomorphically onto the open subspace `U = ∅` of `S`,
and `X'_{/T'}`, `S_{/∅}` and `W` are all the initial fppf sheaf. Here `U = ∅ ≠ S = S ∖ T`. -/
noncomputable def solutionTerminalOfIsEmptyPoints (hX : IsEmpty (Space.points B S hS c.X'))
    [IsIso c.g] :
    Solution c (yoneda.obj (BigFppfOver.terminalObj B S hS)) :=
  let hsrc : IsInitial (Space.completionSheaf B S hS c.X' c.T') :=
    Space.isInitialCompletionSheafOfBotMem B S hS _ _
      (fun U q => Space.bot_mem_of_isEmpty_points hX U q.1.down)
  { isAlgebraicSpace_X := isAlgebraicSpace_yoneda B S hS _
    f := c.toTerminalOfIsEmptyPoints hX
    isProper_f := c.isProper_toTerminalOfIsEmptyPoints hX
    T := ∅
    isClosed_T := isClosed_empty
    preimage_T := Set.preimage_empty.trans
      (Set.eq_empty_of_forall_notMem fun p => hX.elim p).symm
    U := Space.openSubspaceOfPoints B S hS _ ∅
    isOpenSubspace_U := Space.isOpenSubspace_openSubspaceOfPoints B S hS
      (isAlgebraicSpace_yoneda B S hS _) ∅ isOpen_empty
    isoU := c.isoUOfIsEmptyPoints hX
    isoU_comp_ι := Space.openSubspaceOfPointsRestrict_comp_ι B S hS
      (c.toTerminalOfIsEmptyPoints hX) c.T'ᶜ ∅ (fun p _ => hX.elim p)
    a := (Space.isInitialCompletionSheafEmpty B S hS _).uniqueUpToIso (hsrc.ofIso (asIso c.g))
    completion_comp_a := hsrc.hom_ext _ _ }

end IsEmptyPoints

/-! ### The situation `X' = S ⨿ S` -/

/-- The fold map `S ⨿ S ⟶ S`, as a morphism of the big fppf site to its final object. -/
noncomputable abbrev doubleBaseFold :
    BigFppfOver.doubleBase B S hS ⟶ BigFppfOver.terminalObj B S hS :=
  Over.homMk (BigFppfOver.doubleBase B S hS).hom (Category.comp_id _)

/-- The fold map `S ⨿ S ⟶ S` is locally of finite type; it is even finite. -/
theorem locallyOfFiniteType_toScheme_map_doubleBaseFold :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (doubleBaseFold (B := B) (S := S) (hS := hS))) := by
  change LocallyOfFiniteType (B.inclusion.map (B.inclusion.preimage
    (X := B.obj (B.contains_coprod_base hS)) (Y := B.obj hS)
    (coprod.desc (𝟙 (B.inclusion.obj (B.obj hS))) (𝟙 (B.inclusion.obj (B.obj hS))))))
  rw [B.inclusion.map_preimage]
  infer_instance

/-- The structure morphism of `S ⨿ S` to the final object of the site is locally of finite
type. -/
theorem locallyOfFiniteType_toScheme_map_terminal_from_doubleBase :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (terminal.from (BigFppfOver.doubleBase B S hS))) := by
  have : IsIso (terminal.from (BigFppfOver.terminalObj B S hS)) :=
    isIso_of_isTerminal Over.mkIdTerminal terminalIsTerminal _
  have := locallyOfFiniteType_toScheme_map_doubleBaseFold (B := B) (S := S) (hS := hS)
  rw [show terminal.from (BigFppfOver.doubleBase B S hS) =
    doubleBaseFold ≫ terminal.from (BigFppfOver.terminalObj B S hS) from terminal.hom_ext _ _,
    Functor.map_comp]
  infer_instance

/-- `S ⨿ S` is locally Noetherian when `S` is: it is locally of finite type over `S`. -/
theorem isLocallyNoetherian_toScheme_doubleBase (hSN : IsLocallyNoetherian S) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.doubleBase B S hS)) := by
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := hSN
  exact LocallyOfFiniteType.isLocallyNoetherian
    (coprod.desc (𝟙 (B.inclusion.obj (B.obj hS))) (𝟙 (B.inclusion.obj (B.obj hS))))

/-- The identity of the completion of `S ⨿ S` along the empty set is a formal modification, by
Stacks 0GDM for the identity of `S ⨿ S`. -/
theorem isFormalModification_id_completionSheaf_doubleBase (hSN : IsLocallyNoetherian S) :
    FormalSpace.IsFormalModification B S hS
      (𝟙 (Space.completionSheaf B S hS (yoneda.obj (BigFppfOver.doubleBase B S hS)) ∅)) := by
  have hN : Space.IsLocallyNoetherian B S hS (yoneda.obj (BigFppfOver.doubleBase B S hS)) :=
    Space.isLocallyNoetherian_yoneda B S hS _ (isLocallyNoetherian_toScheme_doubleBase hSN)
  have h := FormalSpace.isFormalModification_completionSheafMap
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hN (𝟙 _) ∅
    isClosed_empty (Space.isProper_of_isIso B S hS _) inferInstance
  have e : Space.completionSheafMap B S hS (𝟙 (yoneda.obj (BigFppfOver.doubleBase B S hS))) ∅ =
      𝟙 (Space.completionSheaf B S hS (yoneda.obj (BigFppfOver.doubleBase B S hS)) ∅) :=
    (Space.completionSheafRestrict_self B S hS _ _ le_rfl).symm.trans
      (Space.completionSheafRestrict_id B S hS _ _)
  rwa [e] at h

variable (B S hS) in
/-- **The situation of the counterexample to the final conclusion of Stacks 0GHD.** Over a
locally Noetherian scheme `S`: the algebraic space `X' = S ⨿ S`, the closed subset `T' = ∅`, the
formal algebraic space `W = X'_{/T'}` and the formal modification `g = id`. -/
noncomputable def doubleBaseSituation (hSN : IsLocallyNoetherian S) :
    ContractionSituation B S hS :=
  have hmod := isFormalModification_id_completionSheaf_doubleBase (B := B) (hS := hS) hSN
  have hred := FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace B S hS _
    hmod.isLocallyNoetherian_target.1
  { isLocallyNoetherian_base := hSN
    X' := yoneda.obj (BigFppfOver.doubleBase B S hS)
    isAlgebraicSpace_X' := isAlgebraicSpace_yoneda B S hS _
    isLocallyOfFiniteType_X' :=
      Space.holdsOnEveryEtaleChart_of_isTerminal B S hS
        (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal
        (yoneda.map doubleBaseFold) _
        ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS _).2
          locallyOfFiniteType_toScheme_map_doubleBaseFold)
    T' := ∅
    isClosed_T' := isClosed_empty
    W := Space.completionSheaf B S hS (yoneda.obj (BigFppfOver.doubleBase B S hS)) ∅
    isLocallyNoetherian_W := hmod.isLocallyNoetherian_target
    Wred := hred.choose
    WredInclusion := hred.choose_spec.choose
    isReduction_WredInclusion := hred.choose_spec.choose_spec
    isLocallyOfFiniteType_Wred :=
      isLocallyOfFiniteTypeULift_of_isReduction_completionSheaf _
        locallyOfFiniteType_toScheme_map_terminal_from_doubleBase ∅ isClosed_empty _ _
        hred.choose_spec.choose_spec
    g := 𝟙 _
    isFormalModification_g := hmod }

/-- The solution `X = X' = S ⨿ S` of the situation `(S ⨿ S, ∅, (S ⨿ S)_{/∅}, id)`: the identity of
`X'`, the empty closed subset, the open subspace `U = U'` and the identity of `W`. -/
noncomputable def doubleBaseSituationSolutionSelf (hSN : IsLocallyNoetherian S) :
    Solution (doubleBaseSituation B S hS hSN) (yoneda.obj (BigFppfOver.doubleBase B S hS)) where
  isAlgebraicSpace_X := isAlgebraicSpace_yoneda B S hS _
  f := 𝟙 (yoneda.obj (BigFppfOver.doubleBase B S hS))
  isProper_f := Space.isProper_of_isIso B S hS (𝟙 (yoneda.obj (BigFppfOver.doubleBase B S hS)))
  T := ∅
  isClosed_T := isClosed_empty
  preimage_T := Set.preimage_empty
  U := (doubleBaseSituation B S hS hSN).U'
  isOpenSubspace_U := (doubleBaseSituation B S hS hSN).isOpenSubspace_U'
  isoU := Iso.refl _
  isoU_comp_ι := (Category.id_comp _).trans (Category.comp_id _).symm
  a := Iso.refl _
  completion_comp_a := (Category.comp_id _).trans (Space.completionSheafRestrict_id B S hS _ _)

/-- The open subspace of the solution `X = X'` is the complement of its closed subset, so that
the triples of morphisms `V ⟶ X'` of the proof of Stacks 0GHB are available. -/
theorem range_pointsMap_ι_U_doubleBaseSituationSolutionSelf (hSN : IsLocallyNoetherian S) :
    Set.range (Space.pointsMap B S hS (doubleBaseSituationSolutionSelf hSN).U.toFunctor
      (doubleBaseSituationSolutionSelf (B := B) (hS := hS) hSN).U.ι) =
        (doubleBaseSituationSolutionSelf (B := B) (hS := hS) hSN).Tᶜ :=
  (doubleBaseSituation B S hS hSN).range_pointsMap_ι_U'

/-- Two morphisms `A ⟶ S ⨿ S` through the two inclusions agree only when `A` is empty: the two
inclusions have disjoint images. -/
theorem isEmpty_of_comp_doubleBaseInl_eq {A : BigFppfOver B S hS}
    (h : A ⟶ BigFppfOver.terminalObj B S hS)
    (he : h ≫ BigFppfOver.doubleBaseInl B S hS = h ≫ BigFppfOver.doubleBaseInr B S hS) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := by
  refine ⟨fun a => ?_⟩
  have h1 : (BigFppfOver.toScheme B S hS).map (h ≫ BigFppfOver.doubleBaseInl B S hS) a =
      (BigFppfOver.toScheme B S hS).map (h ≫ BigFppfOver.doubleBaseInr B S hS) a := by
    rw [he]
  have hl : (BigFppfOver.toScheme B S hS).map (BigFppfOver.doubleBaseInl B S hS) =
      coprod.inl := BigFppfOver.doubleBaseInl_left_hom B S hS
  have hr : (BigFppfOver.toScheme B S hS).map (BigFppfOver.doubleBaseInr B S hS) =
      coprod.inr := BigFppfOver.doubleBaseInr_left_hom B S hS
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hl,
    hr] at h1
  exact Set.disjoint_left.mp (isCompl_range_inl_inr _ _).disjoint ⟨_, rfl⟩ ⟨_, h1.symm⟩

end Artin.ContractionSituation

namespace Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **The data of Stacks 0GHD for the two inclusions `S ⟶ S ⨿ S`.** In the situation
`(S ⨿ S, ∅, (S ⨿ S)_{/∅}, id)` over `V = S`, the two elements of `F(S)` are the triples of the
two inclusions `S ⟶ S ⨿ S` in the sense of the proof of Stacks 0GHB (for the solution `X = X'`),
with their witnesses `S ×_{S ⨿ S} (S ⨿ S)`. -/
noncomputable def doubleBaseEqualizer (hSN : IsLocallyNoetherian S) :
    ContractionEqualizer (doubleBaseSituation B S hS hSN) (BigFppfOver.terminalObj B S hS) where
  t₁ := (doubleBaseSituationSolutionSelf hSN).tripleOfHom
    (range_pointsMap_ι_U_doubleBaseSituationSolutionSelf hSN) _
    (yoneda.map (BigFppfOver.doubleBaseInl B S hS))
  t₂ := (doubleBaseSituationSolutionSelf hSN).tripleOfHom
    (range_pointsMap_ι_U_doubleBaseSituationSolutionSelf hSN) _
    (yoneda.map (BigFppfOver.doubleBaseInr B S hS))
  w₁ := (doubleBaseSituationSolutionSelf hSN).witness
    (range_pointsMap_ι_U_doubleBaseSituationSolutionSelf hSN) _
    (yoneda.map (BigFppfOver.doubleBaseInl B S hS))
  w₂ := (doubleBaseSituationSolutionSelf hSN).witness
    (range_pointsMap_ι_U_doubleBaseSituationSolutionSelf hSN) _
    (yoneda.map (BigFppfOver.doubleBaseInr B S hS))

/-- On the equalizer `E'`, the two inclusions `S ⟶ S ⨿ S` agree after `E' ⟶ V`: the witnesses
are the fibre products `S ×_{S ⨿ S} (S ⨿ S)`, and `E'` equalizes their second projections. -/
theorem toBase_comp_yoneda_map_doubleBaseInl (hSN : IsLocallyNoetherian S) :
    (doubleBaseEqualizer B S hS hSN).toBase ≫ yoneda.map (BigFppfOver.doubleBaseInl B S hS) =
      (doubleBaseEqualizer B S hS hSN).toBase ≫ yoneda.map (BigFppfOver.doubleBaseInr B S hS) := by
  let d := doubleBaseEqualizer B S hS hSN
  have h : ∀ f : BigFppfOver.terminalObj B S hS ⟶ BigFppfOver.doubleBase B S hS,
      pullback.fst (yoneda.map f) (𝟙 (yoneda.obj (BigFppfOver.doubleBase B S hS))) ≫
        yoneda.map f =
      pullback.snd (yoneda.map f) (𝟙 (yoneda.obj (BigFppfOver.doubleBase B S hS))) :=
    fun f => by rw [pullback.condition, Category.comp_id]
  have h₁ : d.w₁.p ≫ yoneda.map (BigFppfOver.doubleBaseInl B S hS) = d.w₁.x' := h _
  have h₂ : d.w₂.p ≫ yoneda.map (BigFppfOver.doubleBaseInr B S hS) = d.w₂.x' := h _
  have e₁ : d.toBase ≫ yoneda.map (BigFppfOver.doubleBaseInl B S hS) =
      equalizer.ι d.x₁ d.x₂ ≫ pullback.fst d.w₁.p d.w₂.p ≫ d.w₁.x' := by
    rw [toBase, Category.assoc, Category.assoc, h₁]
    rfl
  have e₂ : d.toBase ≫ yoneda.map (BigFppfOver.doubleBaseInr B S hS) =
      equalizer.ι d.x₁ d.x₂ ≫ pullback.snd d.w₁.p d.w₂.p ≫ d.w₂.x' := by
    rw [toBase, Category.assoc, Category.assoc, pullback.condition_assoc, h₂]
    rfl
  exact e₁.trans ((equalizer.condition d.x₁ d.x₂).trans e₂.symm)

/-- The equalizer `E'` of the two inclusions `S ⟶ S ⨿ S` has no points. -/
theorem isEmpty_points_eqz_doubleBaseEqualizer (hSN : IsLocallyNoetherian S) :
    IsEmpty (Space.points B S hS (doubleBaseEqualizer B S hS hSN).eqz) :=
  Space.isEmpty_points_of_forall_isEmpty fun A e =>
    isEmpty_of_comp_doubleBaseInl_eq ((doubleBaseEqualizer B S hS hSN).toBase.app (op A) e)
      (congrArg (fun φ => φ.app (op A) e) (toBase_comp_yoneda_map_doubleBaseInl hSN))

/-- The closed set `Z = Z₁ ∩ Z₂` of the two inclusions `S ⟶ S ⨿ S` is empty: both are the
inverse images of `T' = ∅`. -/
theorem Z_doubleBaseEqualizer (hSN : IsLocallyNoetherian S) :
    (doubleBaseEqualizer B S hS hSN).Z = ∅ :=
  Set.eq_empty_of_forall_notMem fun z hz => Set.notMem_empty _
    (show Space.pointsMap B S hS _ (yoneda.map (BigFppfOver.doubleBaseInl B S hS)) z ∈
      (∅ : Set (Space.points B S hS (yoneda.obj (BigFppfOver.doubleBase B S hS)))) from hz.1)

/-- The formal modification of the situation of Stacks 0GHD (4) for the two inclusions
`S ⟶ S ⨿ S` is an isomorphism: `E'_{/Z}` is the initial fppf sheaf since `E'` has no points,
and so is `E_W`, which embeds in `S_{/∅}`. -/
theorem isIso_situation_g_doubleBaseEqualizer (hSN : IsLocallyNoetherian S) :
    IsIso ((doubleBaseEqualizer B S hS hSN).situation hSN).g := by
  let d := doubleBaseEqualizer B S hS hSN
  let hsrc : IsInitial (Space.completionSheaf B S hS d.eqz d.centerEqz) :=
    Space.isInitialCompletionSheafOfBotMem B S hS _ _ fun U q => Space.bot_mem_of_isEmpty_points
      (isEmpty_points_eqz_doubleBaseEqualizer (B := B) (hS := hS) hSN) U q.1.down
  let hZ : IsInitial (Space.completionSheaf B S hS
      (yoneda.obj (BigFppfOver.terminalObj B S hS)) d.Z) := by
    rw [show d.Z = ∅ from Z_doubleBaseEqualizer hSN]
    exact Space.isInitialCompletionSheafEmpty B S hS _
  let hEW : IsInitial d.EW := hZ.ofIso
    { hom := hZ.to _
      inv := equalizer.ι d.xhat₁ d.xhat₂
      hom_inv_id := hZ.hom_ext _ _
      inv_hom_id := (cancel_mono (equalizer.ι d.xhat₁ d.xhat₂)).1 (by
        rw [Category.assoc, hZ.hom_ext (hZ.to _ ≫ equalizer.ι d.xhat₁ d.xhat₂) (𝟙 _),
          Category.comp_id, Category.id_comp]) }
  have : IsIso d.completedToEW := ⟨⟨hEW.to _, hsrc.hom_ext _ _, hEW.hom_ext _ _⟩⟩
  have : IsIso ((FormalSpace.smallerBaseSheafFunctor B (BigFppfOver.terminalObj B S hS).left.obj
      S (BigFppfOver.terminalObj B S hS).left.property hS
      (BigFppfOver.terminalObj B S hS).hom).map (d.situation hSN).g) := by
    rw [d.smallerBaseSheafFunctor_map_situation_g hSN]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_inv _))
  exact isIso_of_reflects_iso _ (FormalSpace.smallerBaseSheafFunctor B
    (BigFppfOver.terminalObj B S hS).left.obj S (BigFppfOver.terminalObj B S hS).left.property hS
    (BigFppfOver.terminalObj B S hS).hom)

/-- **The final conclusion of Stacks 0GHD is false as printed.** For the notion of solution of the
prose after Situation 0GH8, read literally
(`AlgebraicGeometry.Artin.ContractionSituation.Solution`: condition (2) asks for *some* open
subspace `U ⊆ E` onto which `f` maps `U'` isomorphically), it is not true that every solution
`E ⟶ V` of the triple of Stacks 0GHD (4) represents `F ×_{Δ, F × F} V` on locally Noetherian
schemes over `V`, as soon as `S` is a nonempty locally Noetherian scheme. For the situation
`(S ⨿ S, ∅, (S ⨿ S)_{/∅}, id)` over `S` and the triples of the two inclusions `S ⟶ S ⨿ S` over
`V = S`, the triple of (4) is `(∅, ∅, ∅ → ∅)`, so `E = V` is a solution (with `T = ∅` and `U = ∅`);
but `Mor_V(V, V)` contains the identity while `F ×_{Δ, F × F} V` has no element over `V`, the two
inclusions being different. -/
theorem not_forall_nonempty_iso_diagonalFibre_of_solution (hSN : IsLocallyNoetherian S)
    [Nonempty S] :
    ¬ ∀ (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
      (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)
      (E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u),
      Solution (d.situation hVN) E →
        Nonempty (morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre) := by
  intro h
  let d := doubleBaseEqualizer B S hS hSN
  let V := BigFppfOver.terminalObj B S hS
  have hX : IsEmpty (Space.points B V.left.obj V.left.property (d.situation hSN).X') :=
    @Equiv.isEmpty _ _ (Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property
      hS V.hom d.E'OverV).toEquiv (isEmpty_points_eqz_doubleBaseEqualizer hSN)
  have := isIso_situation_g_doubleBaseEqualizer (B := B) (hS := hS) hSN
  obtain ⟨α⟩ := h _ V d hSN _ (solutionTerminalOfIsEmptyPoints (d.situation hSN) hX)
  let A : LocallyNoetherianOver B V.left.obj V.left.property :=
    ⟨BigFppfOver.terminalObj B V.left.obj V.left.property, hSN⟩
  let y : d.diagonalFibreObj A.obj := α.hom.app (op A)
    (ULift.up (𝟙 (BigFppfOver.terminalObj B V.left.obj V.left.property)))
  let s := doubleBaseSituationSolutionSelf (B := B) (hS := hS) hSN
  have hU := range_pointsMap_ι_U_doubleBaseSituationSolutionSelf (B := B) (hS := hS) hSN
  let φ : (Over.map V.hom).obj A.obj ⟶ V := toV A.obj
  have heq : s.tripleOfHom hU _ (yoneda.map φ ≫ yoneda.map (BigFppfOver.doubleBaseInl B S hS)) =
      s.tripleOfHom hU _ (yoneda.map φ ≫ yoneda.map (BigFppfOver.doubleBaseInr B S hS)) :=
    (s.tripleOfHom_comp hU φ _).trans
      ((y.2.1.symm.trans y.2.2).trans (s.tripleOfHom_comp hU φ _).symm)
  have hinj := s.tripleOfHom_injective hU ((Over.map V.hom).obj A.obj) hSN heq
  rw [← Functor.map_comp, ← Functor.map_comp] at hinj
  exact (isEmpty_of_comp_doubleBaseInl_eq φ (yoneda.map_injective hinj)).false
    (Classical.arbitrary S)

end Artin.ContractionEqualizer

end AlgebraicGeometry

end

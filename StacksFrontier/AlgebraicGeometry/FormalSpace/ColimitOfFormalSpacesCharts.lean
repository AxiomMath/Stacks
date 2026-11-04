module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitStageThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallySurjectiveAlongThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSetTheoreticConditionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitLocalFactorization

/-!
# The chart system of Stacks 0GVN

Let `S` be a scheme contained in a big fppf site `B` and let `(X_λ, f_{λμ})` be a directed
system of *formal* algebraic spaces over `S` in which every transition morphism
`f_{λμ} : X_λ ⟶ X_μ` is a closed immersion inducing an isomorphism `X_{λ,red} ⟶ X_{μ,red}`.
**Stacks 0GVN** says that the colimit `X = colim_λ X_λ`, formed among fppf sheaves, is again a
formal algebraic space over `S`.

The source argument is a reduction to the affine case. Fix one index `λ` and an atlas
`{X_{k,λ} ⟶ X_λ}` as in Definition 0AIM. The étale affine formal chart `X_{k,λ}` of `X_λ` is
transported along the thickenings to a compatible étale affine formal chart `X_{k,μ}` of every
later stage, these base change from one another, and `X_k = colim_μ X_{k,μ}` is an affine formal
algebraic space by **Stacks 0GVM**. The family `{X_k ⟶ X}` is then an atlas of `X`. This module
constructs that chart system and assembles the atlas; the set-theoretic condition of Stacks 0AIS
for the colimit, clause (4) of Definition 0AIM, is a hypothesis here and is proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpacesAdmissible`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_iso_colimit_baseChangeDiagram`: a sheaf over a directed
  colimit of fppf sheaves is the colimit of its base changes to the stages, cartesianly.
* `AlgebraicGeometry.FormalSpace.isPullback_chartSystem_map` and
  `AlgebraicGeometry.FormalSpace.isThickening_chartSystem_map`: the transition morphisms of each
  chart diagram inherit the thickening condition from those of the base.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_colimMap_of_chartSystem` and
  `AlgebraicGeometry.FormalSpace.isFormalAtlas_colimMap_of_chartSystem`: the chart colimits are
  representable étale over the colimit and form an atlas as in (1)–(3) of Definition 0AIM.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem_of_stageCover`: the
  assembly from a covering at one stage.
* `AlgebraicGeometry.FormalSpace.exists_chartSystem_of_stageAtlas`: the chart system built from
  an atlas of one stage (private), using the étale lift of Stacks 0DEG and, for the affineness
  of its stages, Stacks 0DE8 with
  `AlgebraicGeometry.FormalSpace.IsAffineOfSurjectiveClosedImmersion`.
*
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_of_setTheoretic`:
  Stacks 0GVN given the set-theoretic condition for the colimit and
  `IsAffineOfSurjectiveClosedImmersion`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0DE8](https://stacks.math.columbia.edu/tag/0DE8)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart system is cartesian over its base diagram.** If each square of `α k : G k ⟶ E`
against the colimit cocones is cartesian, then each square of `α k` over a transition morphism
`E.map g` is cartesian too: the square over `g : i ⟶ j` pastes with the cartesian square at `j`
to the cartesian square at `i`, so `CategoryTheory.IsPullback.of_right` applies. In particular
`(G k).map g` is a base change of `E.map g`, which is how the chart diagrams inherit from `E`
whatever property of its transition morphisms is stable under base change. -/
theorem isPullback_chartSystem_map
    {Λ : Type (u + 1)} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (k : I) ⦃i j : Λ⦄ (g : i ⟶ j) :
    IsPullback ((G k).map g) ((α k).app i) ((α k).app j) (E.map g) := by
  refine IsPullback.of_right ?_ ((α k).naturality g) (hsq k j)
  rw [colimit.w (G k) g, colimit.w E g]
  exact hsq k i

/-- **The transition morphisms of a chart diagram are representable thickenings, as soon as
those of the base diagram are.** This is `AlgebraicGeometry.FormalSpace.isPullback_chartSystem_map`
followed by stability of a relative morphism property under base change, with the two renderings
of representability compared by
`AlgebraicGeometry.FormalSpace.relative_sheafifiedYoneda_iff_uliftYoneda`. It is why the chart
system of Stacks 0GVN asserts nothing about the transition morphisms of its chart diagrams: the
hypothesis Stacks 0GVM needs of them follows from the cartesian squares. -/
theorem isThickening_chartSystem_map
    {Λ : Type (u + 1)} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (k : I) ⦃i j : Λ⦄ (g : i ⟶ j) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ((G k).map g) :=
  (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ ((G k).map g)).mpr
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((isPullback_chartSystem_map B S hS E G α hsq k g).flip.map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) (hthick g))

/-- **A sheaf over a directed colimit of fppf sheaves is the colimit of its base changes to the
stages, cartesianly.** For `v : V ⟶ colim E` with `E` a directed system of fppf sheaves over
`S`, the diagram `i ↦ E_i ×_{colim E} V` of base changes has `V` for its colimit, and the
squares
```
E_i ×_{colim E} V ⟶ colim_j (E_j ×_{colim E} V)
       ↓                        ↓
      E_i          ⟶          colim E
```
are cartesian, the right-hand morphism being the one induced by the projections.

This is the chart diagram of the proof of Stacks 0GVN, and it is why that proof needs to assume
nothing about its chart diagrams beyond what `v` already provides: a filtered colimit of sheaves
of sets is a *universal* colimit
(`CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`), a nonempty directed preorder
is filtered, and the base change of a universal colimit cocone along a morphism into its vertex
is again a colimit cocone
(`CategoryTheory.Limits.coconePointIsoColimitBaseChange`). -/
theorem exists_iso_colimit_baseChangeDiagram
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS) {V : FppfSheaf B S hS} (v : V ⟶ colimit E) :
    ∃ e : V ≅ colimit (Limits.baseChangeDiagram (colimit.cocone E) v),
      colimMap (Limits.baseChangeπ (colimit.cocone E) v) = e.inv ≫ v ∧
      ∀ i : Λ, IsPullback (colimit.ι (Limits.baseChangeDiagram (colimit.cocone E) v) i)
        ((Limits.baseChangeπ (colimit.cocone E) v).app i)
        (colimMap (Limits.baseChangeπ (colimit.cocone E) v)) (colimit.ι E i) := by
  have hu : IsUniversalColimit (colimit.cocone E) :=
    Limits.sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology B S hS) E
  have hinv : ∀ i : Λ, colimit.ι (Limits.baseChangeDiagram (colimit.cocone E) v) i ≫
      (Limits.coconePointIsoColimitBaseChange (colimit.cocone E) v hu).inv =
      (Limits.baseChangeCocone (colimit.cocone E) v).ι.app i := fun i ↦
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (Limits.isColimitBaseChangeCocone (colimit.cocone E) v hu) (colimit.isColimit _) i
  have hmap : colimMap (Limits.baseChangeπ (colimit.cocone E) v) =
      (Limits.coconePointIsoColimitBaseChange (colimit.cocone E) v hu).inv ≫ v := by
    refine colimit.hom_ext (fun i ↦ ?_)
    rw [ι_colimMap, ← Category.assoc, hinv i]
    exact pullback.condition (f := colimit.ι E i) (g := v)
  refine ⟨Limits.coconePointIsoColimitBaseChange (colimit.cocone E) v hu, hmap, fun i ↦ ?_⟩
  refine (Limits.isPullback_baseChangeCocone_ι (colimit.cocone E) v i).of_iso (Iso.refl _)
    (Limits.coconePointIsoColimitBaseChange (colimit.cocone E) v hu) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.isColimitBaseChangeCocone (colimit.cocone E) v hu) (colimit.isColimit _) i
  · simp
  · simp [hmap]
  · simp

/-- **Each chart colimit is representable étale over the colimit.** With the chart system of
Stacks 0GVN — morphisms `α k : G k ⟶ E` of diagrams of fppf sheaves over `S` whose components
are representable étale and whose squares against the colimit cocones are cartesian — the
induced morphism `colim (G k) ⟶ Z` is representable étale for any sheaf `Z` identified with
`colim E`, granted the representability clause `hrep`.

The étale clause is proved, not granted: the transition morphisms of `E` being representable
thickenings makes them monomorphisms, so a scheme-valued point of `colim E` out of a
*quasi-compact* object of the site factors through a stage
(`AlgebraicGeometry.FormalSpace.exists_factor_through_stage_of_compact`), and
étaleness of a base change is Zariski local on the test object
(`AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_of_affine`), so the affine opens of
an arbitrary point suffice. It is the step of the assembly which also discharges the
set-theoretic condition of Stacks 0AIS for `colim (G k)`, that condition descending along a
representable morphism. -/
theorem isRepresentableEtale_colimMap_of_chartSystem
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (hrep : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ k : I, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (colimMap (α k)).hom)
    (Z : FppfSheaf B S hS) (eZ : Z ≅ colimit E) (k : I) :
    IsRepresentableEtale B S hS (colimMap (α k) ≫ eZ.inv) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine isRepresentableEtale_of_compact_stageSquares B S hS (colimMap (α k) ≫ eZ.inv)
    (fun i ↦ colimit.ι (G k) i) (fun i ↦ (α k).app i)
    (fun i ↦ colimit.ι E i ≫ eZ.inv) (hαet k) (fun i ↦ ?_) (fun T hT θ ↦ ?_) ?_
  · exact (hsq k i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ.symm
      (by simp) (by simp) (by simp) (by simp)
  · -- a quasi-compact point of the colimit factors through a stage
    -- (`exists_factor_through_stage_of_compact`), read on presheaves
    have := hT
    obtain ⟨i, ξ', hξ'⟩ := exists_factor_through_stage_of_compact B S hS E
      (fun _ _ g ↦ mono_of_isRepresentableThickening B S hS (E.map g) (hthick g)) T
      (⟨θ ≫ eZ.hom.hom⟩ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ colimit E)
    let θ' : (uliftYoneda.{u + 1}).obj T ⟶ (E.obj i).obj := ξ'.hom
    refine ⟨i, θ', ?_⟩
    have hθ : θ ≫ eZ.hom.hom = θ' ≫ (colimit.ι E i).hom :=
      congrArg (fun m ↦ m.hom) hξ'
    have h : (colimit.ι E i ≫ eZ.inv).hom = (colimit.ι E i).hom ≫ eZ.inv.hom := rfl
    rw [h, ← Category.assoc, ← hθ]
    simp
  · exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS
      (colimMap (α k)).hom eZ.inv.hom (hrep k)
      (isRepresentableEtale_of_isIso B S hS eZ.inv).1

/-- **The chart colimits form an atlas as in conditions (1), (2) and (3) of Definition 0AIM.**
This is the assembly step of Stacks 0GVN with the set-theoretic condition of Stacks 0AIS
*removed from both sides*: what a chart system produces is conditions (1), (2) and (3) for the
family `{colim (G k) ⟶ Z}`, and the condition of Stacks 0AIS is the remaining conjunct of
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace`, which this says nothing about. Stating
it separately is what lets the condition for `Z` be *deduced* from the atlas under a bound on
its index (`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`)
rather than only assumed.

The covering hypothesis is asked at a single stage only. At every later stage it is a
consequence, by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_isRepresentableThickening`: the
transition morphism `E.obj i₀ ⟶ E.obj m` is a representable thickening, the charts over the two
stages are compatible with it by naturality of `α k`, and the charts over `E.obj m` are
representable étale. Stages above `i₀` suffice, because the index is directed and a colimit
injection factors through any later one. -/
theorem isFormalAtlas_colimMap_of_chartSystem
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (i₀ : Λ)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i₀)))
    (hrep : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ k : I, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (colimMap (α k)).hom)
    (Z : FppfSheaf B S hS) (eZ : Z ≅ colimit E) :
    IsFormalAtlas B S hS Z (fun k ↦ colimit (G k)) (fun k ↦ colimMap (α k) ≫ eZ.inv) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the charts cover every stage above `i₀`: local surjectivity ascends along the thickening
  have hcovUp : ∀ n : Λ, i₀ ≤ n →
      Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app n)) := fun n hn ↦
    isLocallySurjective_sigmaDesc_of_isRepresentableThickening B S hS
      (E.map (homOfLE hn)) (hthick (homOfLE hn)) (fun k ↦ (α k).app i₀)
      (fun k ↦ (α k).app n) (fun k ↦ (G k).map (homOfLE hn))
      (fun k ↦ ((α k).naturality (homOfLE hn)).symm) (fun k ↦ hαet k n) hcov
  refine ⟨haff,
    isRepresentableEtale_colimMap_of_chartSystem B S hS E hthick G α hαet hsq hrep Z eZ, ?_⟩
  -- the chart colimits cover `Z`
  rw [Sheaf.isLocallySurjective_iff_epi]
  refine ⟨fun k l hkl ↦ ?_⟩
  have hζkl : ∀ m : I, (colimMap (α m) ≫ eZ.inv) ≫ k = (colimMap (α m) ≫ eZ.inv) ≫ l :=
    fun m ↦ by simpa using congrArg (Sigma.ι (fun m : I ↦ colimit (G m)) m ≫ ·) hkl
  have hstage : ∀ n : Λ, i₀ ≤ n →
      colimit.ι E n ≫ eZ.inv ≫ k = colimit.ι E n ≫ eZ.inv ≫ l := by
    intro n hn
    have hepi : Epi (Sigma.desc (fun m ↦ (α m).app n)) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp (hcovUp n hn)
    refine (cancel_epi (Sigma.desc (fun m ↦ (α m).app n))).1 (Sigma.hom_ext _ _ (fun m ↦ ?_))
    simpa using congrArg (colimit.ι (G m) n ≫ ·) (hζkl m)
  have hcolim : eZ.inv ≫ k = eZ.inv ≫ l := by
    refine colimit.hom_ext (fun i ↦ ?_)
    obtain ⟨n, hin, hi₀n⟩ := exists_ge_ge i i₀
    rw [← colimit.w E (homOfLE hin), Category.assoc, Category.assoc, hstage n hi₀n]
  exact (cancel_epi eZ.inv).1 hcolim

/-- The assembly step of Stacks 0GVN with the covering clause asked at **one** stage. Let `E` be
a directed diagram of fppf sheaves over `S` whose transition morphisms are representable
thickenings, and let `G` be a family of diagrams on the same index with morphisms
`α k : G k ⟶ E` such that each `(α k).app i` is representable étale, each square

```
(G k).obj i ⟶ colim (G k)
     ↓               ↓
   E.obj i    ⟶    colim E
```

is cartesian, and the `(α k).app i₀` jointly cover `E.obj i₀` for **one** index `i₀`. If
moreover each `colim (G k)` is an affine formal algebraic space and each
`colim (G k) ⟶ colim E` is representable by algebraic spaces, then a sheaf `Z` isomorphic to
`colim E` which satisfies the set-theoretic condition of Stacks 0AIS is a formal algebraic space
over `S`: the morphisms `colim (G k) ⟶ Z` form an atlas as in Definition 0AIM.

The covering hypothesis is asked at a single stage only. At every later stage it is a
consequence, by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_isRepresentableThickening`: the
transition morphism `E.obj i₀ ⟶ E.obj m` is a representable thickening, the charts over the two
stages are compatible with it by naturality of `α k`, and the charts over `E.obj m` are
representable étale. Stages above `i₀` suffice, because the index is directed and a colimit
injection factors through any later one.

Unlike `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem` this asks no
factorization of a scheme-valued point of the colimit through a stage: the étale clause of
Definition 0AIM is proved from `hthick` alone, the factorization being a theorem at the
quasi-compact objects. The price is `hrep`, the representability clause for the chart colimits,
which that form derives from its factorization hypothesis. -/
theorem isFormalAlgebraicSpace_of_chartSystem_of_stageCover
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (i₀ : Λ)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i₀)))
    (hrep : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ k : I, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (colimMap (α k)).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  obtain ⟨eZ⟩ := hZ
  exact ⟨hZset, I, (fun k ↦ colimit (G k)), (fun k ↦ colimMap (α k) ≫ eZ.inv),
    isFormalAtlas_colimMap_of_chartSystem B S hS E hthick G α haff hαet hsq i₀ hcov hrep Z eZ⟩

/-- **Stacks 0GVN from a granted chart system**, for a caller who has one. Let `E` be a directed
system of formal algebraic spaces over `S` whose transition morphisms are representable
thickenings — equivalently, by Stacks 0GVL, closed immersions inducing isomorphisms on
reductions. A sheaf `Z` isomorphic to its colimit, satisfying the set-theoretic condition of
Stacks 0AIS and admitting a system of affine étale charts of the stages, is a formal algebraic
space over `S`.

`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_of_setTheoretic`
is the form
of the tag that **constructs** this chart system, from the atlas of a single stage and the étale
lift of Stacks 0DEG; it is what carries the registration. This form is kept because its
hypotheses are incomparable with that one's: it does not ask that the colimit injections be
representable thickenings, and it is instantiable from any chart system whatever. Its proof is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem_of_stageCover` with the
chart colimits recognised as affine formal algebraic spaces by Stacks 0GVM
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit`).

The charts are the hypotheses `G`, `α`, `hGaff`, `hαet`, `hsq` and `hcov`; `hrep` is the
representability clause of Definition 0AIM for the chart colimits, which is the set-theoretic
half of that clause. What is proved is the passage from the stages to the colimit: each chart
colimit is an affine formal algebraic space by Stacks 0GVM, each is *étale* over `Z` — that
needs no hypothesis beyond `hthick`, the factorization of a quasi-compact point through a stage
being a theorem and étaleness being Zariski local on the test object — and these colimits form
an atlas of `Z` in the sense of Definition 0AIM. The set-theoretic condition of Stacks 0AIS that
Stacks 0GVM needs for each chart colimit is proved rather than assumed: each chart colimit is
representable étale over `Z`, and the condition descends along a representable morphism.

**No hypothesis is asked of the transition morphisms of the chart diagrams.** The condition
Stacks 0GVM consumes of them follows from `hsq` and `hthick`, by
`AlgebraicGeometry.FormalSpace.isThickening_chartSystem_map`: a chart system is cartesian over
its base diagram, so `(G k).map g` is a base change of `E.map g`.

**`hcov` is asked at one stage only.** The source gets it at the stage whose atlas the charts
come from, and at every other stage it is a *consequence*: local surjectivity of a family of
representable étale morphisms ascends along a representable thickening
(`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_isRepresentableThickening`),
and the transition morphisms of `E` are representable thickenings by `hthick`. That residue is
what keeps the chart system from being vacuous: with `I` empty every other chart hypothesis
holds for trivial reasons.

The hypothesis `_hform` that the stages be formal algebraic spaces is consumed by the chart
hypotheses here and so goes unused; in the constructed form of the tag it is what supplies the
charts. -/
theorem isFormalAlgebraicSpace_of_colimit_closedImmersions_of_chartSystem
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (_hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (I : Type (u + 1)) (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hGaff : ∀ (k : I) (i : Λ), IsAffineFormalAlgebraicSpace B S hS ((G k).obj i))
    (hαet : ∀ (k : I) (i : Λ), IsRepresentableEtale B S hS ((α k).app i))
    (hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (i₀ : Λ)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i₀)))
    (hrep : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ k : I, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (colimMap (α k)).hom)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  obtain ⟨eZ⟩ := hZ
  refine isFormalAlgebraicSpace_of_chartSystem_of_stageCover B S hS E hthick G α (fun k ↦ ?_)
    hαet hsq i₀ hcov hrep Z hZset ⟨eZ⟩
  -- each chart diagram is a directed system of affine formal algebraic spaces along
  -- representable thickenings, so Stacks 0GVM makes its colimit an affine formal algebraic
  -- space; the set-theoretic condition of Stacks 0AIS for that colimit is not a hypothesis, it
  -- descends from `hZset` along the representable étale morphism `colim (G k) ⟶ Z`
  exact isAffineFormalAlgebraicSpace_colimit B S hS (G k) (hGaff k)
    (isThickening_chartSystem_map B S hS E hthick G α hsq k)
    (colimit (G k)) (Iso.refl _)
    (satisfiesSetTheoreticCondition_source_of_isRepresentableByAlgebraicSpacesULift B S hS
      (colimMap (α k) ≫ eZ.inv)
      (isRepresentableEtale_colimMap_of_chartSystem B S hS E hthick G α hαet hsq hrep
        Z eZ k).1 hZset)

/-- **The chart system of the proof of Stacks 0GVN, constructed from an atlas of one stage.**
Given an atlas `{Y k ⟶ E_{i₀}}` of a single stage by affine formal algebraic spaces, each member
`p k` is carried to a chart of the colimit by the étale lift of **Stacks 0DEG** — the dependent
product `U_{Y k, p k} ⟶ colim E` of `AlgebraicGeometry.FormalSpace.liftAlongBase` — and the
diagram of its base changes to the stages is a chart diagram satisfying every clause the chart
system of this tag used to assert: the cartesian squares, affineness of the stages, representable
étaleness over each stage, the covering clause at `i₀`, and the representability clause for the
chart colimit.

The construction is the whole geometric content of the tag's proof. It takes no set-theoretic
hypothesis on the colimit:
the chart colimits are not asserted here to be affine formal algebraic spaces, only their
stages are, and it is the passage from the stages to the colimit by Stacks 0GVM that needs the
condition. -/
private theorem exists_chartSystem_of_stageAtlas
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (hthickAff : IsAffineOfSurjectiveClosedImmersion B S hS) (i₀ : Λ)
    (K : Type (u + 1)) (Y : K → FppfSheaf B S hS) (p : ∀ k, Y k ⟶ E.obj i₀)
    (hYaff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (Y k))
    (hpet : ∀ k, IsRepresentableEtale B S hS (p k))
    (hcov₀ : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (G : K → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E),
      (∀ (k : K) (i : Λ), IsAffineFormalAlgebraicSpace B S hS ((G k).obj i)) ∧
      (∀ (k : K) (i : Λ), IsRepresentableEtale B S hS ((α k).app i)) ∧
      (∀ (k : K) (i : Λ), IsPullback (colimit.ι (G k) i) ((α k).app i)
        (colimMap (α k)) (colimit.ι E i)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i₀)) ∧
      (∀ k : K, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (colimMap (α k)).hom) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the colimit injections are representable thickenings: the stages are formal algebraic
  -- spaces, so their sections are pointwise `u`-small by Stacks 0AIS, and the local
  -- representing objects over the affine opens of a test object glue under the size bound a
  -- thickening carries
  have hι : ∀ i : Λ,
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (colimit.ι E i).hom :=
    isRepresentableThickeningULift_colimitι_of_small B S hS E hthick
      (fun i ↦ small_of_isFormalAlgebraicSpace B S hS (hform i))
  -- the chart of the colimit attached to each atlas member, by the étale lift of Stacks 0DEG
  have hvet : ∀ k : K, IsRepresentableEtale B S hS
      (liftAlongBase B S hS (colimit.ι E i₀) (p k)) := fun k ↦
    isRepresentableEtale_liftAlongBase B S hS (hι i₀) (hpet k)
  -- a filtered colimit of sheaves of sets is universal, so each chart is the colimit of its
  -- own base changes to the stages, cartesianly; those base changes are the chart diagram
  choose ebc hcolimMap hsq using fun k : K ↦ exists_iso_colimit_baseChangeDiagram B S hS E
    (liftAlongBase B S hS (colimit.ι E i₀) (p k))
  have hpb := fun (k : K) (i : Λ) ↦ Limits.isPullback_baseChangeCocone_ι (colimit.cocone E)
    (liftAlongBase B S hS (colimit.ι E i₀) (p k)) i
  have hαet : ∀ (k : K) (i : Λ), IsRepresentableEtale B S hS
      ((Limits.baseChangeπ (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k))).app i) := fun k i ↦
    isRepresentableEtale_of_isPullback B S hS (hpb k i) (hvet k)
  -- each stage of a chart diagram is an *affine* formal algebraic space, by Stacks 0DE8
  have hGaff : ∀ (k : K) (j : Λ), IsAffineFormalAlgebraicSpace B S hS
      ((Limits.baseChangeDiagram (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k))).obj j) := by
    intro k j
    refine isAffineFormalAlgebraicSpace_of_iso B S hS
      (pullbackSymmetry (liftAlongBase B S hS (colimit.ι E i₀) (p k)) (colimit.ι E j)) ?_
    exact (isAffineFormalAlgebraicSpace_pullback_liftAlongBase B S hS E hform hι (p k)
      (hYaff k) (hpet k) hthickAff).2 j
  -- the representability clause of Definition 0AIM: each chart colimit *is* the chart
  have hrep : ∀ k : K, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (colimMap (Limits.baseChangeπ (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k)))).hom := by
    intro k
    rw [hcolimMap k]
    exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS (ebc k).inv.hom
      (liftAlongBase B S hS (colimit.ι E i₀) (p k)).hom
      (isRepresentableEtale_of_isIso B S hS (ebc k).inv).1 (hvet k).1
  -- the charts cover the stage whose atlas they come from: their base changes to it are the
  -- atlas members, by Stacks 0DEG again
  have hinj : ∀ A : BigFppfOver B S hS,
      Function.Injective ((colimit.ι E i₀).hom.app (Opposite.op A)) := fun A ↦
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_of_isRepresentableThickeningULift B S hS (hι i₀)) (Opposite.op A))
  have hεex : ∀ k : K, ∃ e : Y k ≅ (Limits.baseChangeDiagram (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k))).obj i₀,
      e.hom ≫ (Limits.baseChangeπ (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k))).app i₀ = p k := by
    intro k
    exact ⟨_, (isPullback_liftAlongSection B S hS hinj (p := p k)).isoIsPullback_hom_snd _ _
      (hpb k i₀)⟩
  choose ε hε using hεex
  have hcov : Sheaf.IsLocallySurjective (Sigma.desc (fun k : K ↦
      (Limits.baseChangeπ (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p k))).app i₀)) := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    have hep : Epi (Sigma.desc p) := (Sheaf.isLocallySurjective_iff_epi _).mp hcov₀
    refine epi_of_epi_fac (f := Sigma.desc (fun k : K ↦ (ε k).hom ≫
      Sigma.ι (fun m : K ↦ (Limits.baseChangeDiagram (colimit.cocone E)
        (liftAlongBase B S hS (colimit.ι E i₀) (p m))).obj i₀) k))
      (h := Sigma.desc p) ?_
    refine Sigma.hom_ext _ _ (fun k ↦ ?_)
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
    exact hε k
  exact ⟨fun k ↦ Limits.baseChangeDiagram (colimit.cocone E)
      (liftAlongBase B S hS (colimit.ι E i₀) (p k)),
    fun k ↦ Limits.baseChangeπ (colimit.cocone E)
      (liftAlongBase B S hS (colimit.ι E i₀) (p k)),
    hGaff, hαet, hsq, hcov, hrep⟩

/-- **Stacks 0GVN, given the set-theoretic condition.** Let `S` be a scheme contained in a big
fppf site `B` and let `E` be a
directed system of formal algebraic spaces over `S` whose transition morphisms are representable
thickenings — equivalently, by Stacks 0GVL, closed immersions inducing isomorphisms on
reductions. A sheaf `Z` isomorphic to the colimit of `E` and satisfying the set-theoretic
condition of Stacks 0AIS is a formal algebraic space over `S`.

**The chart system of the source proof is constructed here, not granted.** The atlas of one
stage is what Definition 0AIM gives for `E_{i₀}` — it is `hform` that supplies it, so that
hypothesis of the tag is now used rather than inert — and each of its members `p : Y ⟶ E_{i₀}`
is carried to a chart of the colimit by the étale lift of **Stacks 0DEG**, as the dependent
product `U_{Y, p} ⟶ colim E` of `AlgebraicGeometry.FormalSpace.liftAlongBase`, which is
representable étale by `AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongBase`. Its
base changes to the stages form the chart diagram, `CategoryTheory.Limits.baseChangeDiagram`,
and every clause the chart system used to assert is then a theorem:

* the cartesian squares against the colimit cocones, because a filtered colimit of sheaves of
  sets is a *universal* colimit
  (`CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`), so the chart is the
  colimit of its own base changes
  (`CategoryTheory.Limits.coconePointIsoColimitBaseChange`);
* representable étaleness of each projection to a stage, that being a base change of
  `U_{Y, p} ⟶ colim E`;
* the thickening condition on the transition morphisms of the chart diagram, by
  `AlgebraicGeometry.FormalSpace.isThickening_chartSystem_map`;
* affineness of the chart diagram's stages, by **Stacks 0DE8** through
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_liftAlongBase` — this is
  what the single hypothesis `hthickAff` is for: Stacks 07VS for a surjective closed immersion
  from an affine object of the site,
  `AlgebraicGeometry.FormalSpace.IsAffineOfSurjectiveClosedImmersion`;
* the covering clause, because the charts over `E_{i₀}` are the atlas of `E_{i₀}` — their
  sources are canonically the base changes of the charts to that stage, by
  `AlgebraicGeometry.FormalSpace.isPullback_liftAlongSection`;
* the representability clause `hrep` of Definition 0AIM for the chart colimits, each chart
  colimit being the chart itself.

**That the colimit injections are representable thickenings is also proved, not granted.** It
was the hypothesis `hι`, and is now
`AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_colimitι_of_small`: the stages are
formal algebraic spaces, so their sections are pointwise `u`-small by Stacks 0AIS
(`AlgebraicGeometry.FormalSpace.small_of_isFormalAlgebraicSpace`), the factorization of a
*quasi-compact* point through a stage is a theorem, and the local representing objects — closed
subschemes of the test object, because a thickening base-changes to a surjective closed immersion
— glue by `AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`. So
`hform` is used twice.

So the only hypotheses beyond those of Stacks 0GVN are `hZset` and `hthickAff`. `hZset` is
proved for an index admitting coproducts in the site by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_admissible`, which
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_closedImmersions_of_admissible`
combines with this statement. -/
theorem isFormalAlgebraicSpace_of_colimit_of_setTheoretic
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (hthickAff : IsAffineOfSurjectiveClosedImmersion B S hS)
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  obtain ⟨i₀⟩ := ‹Nonempty Λ›
  -- the atlas of one stage, which Definition 0AIM supplies through `hform`
  obtain ⟨-, K, Y, p, hYaff, hpet, hcov₀⟩ := hform i₀
  obtain ⟨G, α, hGaff, hαet, hsq, hcov, hrep⟩ := exists_chartSystem_of_stageAtlas B S hS Λ E
    hform hthick hthickAff i₀ K Y p hYaff hpet hcov₀
  exact isFormalAlgebraicSpace_of_colimit_closedImmersions_of_chartSystem B S hS Λ E hform
    hthick K G α hGaff hαet hsq i₀ hcov hrep Z hZset hZ

end AlgebraicGeometry.FormalSpace

end

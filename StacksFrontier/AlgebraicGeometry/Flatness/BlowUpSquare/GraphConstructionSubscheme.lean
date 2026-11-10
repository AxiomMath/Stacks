module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstructionTriple
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback

/-!
# The closed subscheme of the fibre at infinity of the graph construction

Let `f : X ⟶ S` be a morphism of schemes and `E` a perfect object of `D(𝒪_X)`.  The graph
construction of Section 0F8Z applies Stacks tag 0GTY to the triple
`(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`, `p : 𝐏¹_X ⟶ X` the projection, producing `b : W ⟶ 𝐏¹_X`, the fibre
at infinity `W_∞ = b⁻¹((𝐏¹_X)_∞)` and `Q = Lη_ℐ Lb^*Lp^*E`.  This file proves clauses (3) and (4)
of Stacks tag 0F90: there is a closed immersion `t : T ⟶ W_∞` of finite presentation such that
the cohomology sheaves of `Lt^*Q` are finite locally free, every point of `W_∞` lying over the
open `U ⊆ X` where the cohomology sheaves of `E` are locally free lies in `T`, and at a point of
`T` over `U` the rank of `H^n(Lt^*Q)` is the rank of `H^n(E)`.

`T` is the closed subscheme of Stacks tag 0F8X for the triple of the graph construction, carried
into `W_∞` by the identification of the closed subscheme of `W` cut out by the pullback of the
ideal of `(𝐏¹_X)_∞` with the fibre product `W ×_{𝐏¹_X} X`.

## Main results

* `Stacks.Chow.exists_closedImmersion_graphObjectRestrict`: **Stacks tag 0F90, clauses (3) and
  (4)**.
* `Stacks.Chow.graphFibreAtInfinityIso`: the fibre at infinity is the closed subscheme of `W` cut
  out by the pullback of the divisor at infinity.
* `Stacks.Chow.le_locallyFreeLocus_graphTriple`: the inverse image in `𝐏¹_X` of an open over
  which the cohomology sheaves of `E` are finite locally free lies in the locally free locus of
  the triple of the graph construction.

## Implementation notes

Clause (3) is stated set-theoretically and for every open `V ⊆ X` over which all the cohomology
sheaves of `E` are finite locally free, which together say that every point of `W_∞` over `U`
lies in `T`.  Clause (4) is stated at points of `T` over such an open `V`, as in the source,
where `U` is the locus on which every cohomology sheaf of `E` is locally free.

## References

* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry

/-- An open subscheme over which an ideal sheaf vanishes lies in the closed subscheme it cuts
out. -/
theorem Scheme.IdealSheafData.mem_range_subschemeι_of_comap_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens) (h : I.comap U.ι = ⊥) {x : X} (hx : x ∈ U) :
    x ∈ Set.range I.subschemeι := by
  have hs := congrArg (fun J : U.toScheme.IdealSheafData => J.support) h
  simp only [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_bot] at hs
  rw [I.range_subschemeι]
  have : (⟨x, hx⟩ : U.toScheme) ∈ (⊤ : TopologicalSpace.Closeds U.toScheme) := trivial
  rw [← hs] at this
  exact this

/-- A module whose restriction to an open is finite locally free is finite locally free over that
open, in the sense of `AlgebraicGeometry.RingedSpace.IsFiniteLocallyFreeOver`. -/
theorem RingedSpace.isFiniteLocallyFreeOver_of_restrict {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj F)) :
    RingedSpace.IsFiniteLocallyFreeOver (X := X.toRingedSpace) F U := by
  intro x hx
  obtain ⟨V, hV, I, hI, ⟨e⟩⟩ := ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr h) ⟨x, hx⟩
  have hr : Set.range (U.ι ''ᵁ V).ι.base ⊆ Set.range (V.ι ≫ U.ι).base := by
    simp [Set.range_comp]
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset (V.ι ≫ U.ι)
    (U.ι ''ᵁ V).ι F I hr ((Scheme.Modules.restrictFunctorComp V.ι U.ι).app F ≪≫ e)
  exact ⟨U.ι ''ᵁ V, ⟨⟨x, hx⟩, hV, rfl⟩, Scheme.Opens.ι_image_le _ _, I, hI,
    ⟨(RingedSpace.restrictModulesIsoRestrictFunctor X _).app F ≪≫ e'⟩⟩

/-- **The closed subscheme cut out by the pullback of the ideal of a closed immersion `i` along
`b` is the fibre product of `b` and `i`.** -/
def Scheme.Hom.kerComapIso {X Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (b : X ⟶ Y) : (i.ker.comap b).subscheme ≅ pullback b i :=
  i.ker.comapIso b ≪≫ asIso (pullback.map b i.ker.subschemeι b i (𝟙 _) (inv i.toImage) (𝟙 _)
    (by simp) (by rw [Category.comp_id, IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]))

/-- The identification of `kerComapIso` lies over `X`. -/
theorem Scheme.Hom.kerComapIso_hom_fst {X Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (b : X ⟶ Y) : (i.kerComapIso b).hom ≫ pullback.fst b i = (i.ker.comap b).subschemeι := by
  rw [kerComapIso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_fst,
    Category.comp_id, Scheme.IdealSheafData.comapIso_hom_fst]

end AlgebraicGeometry

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)

/-- The fibre at infinity `W_∞` of the graph construction is the closed subscheme of `W` cut out
by the pullback of the divisor at infinity. -/
def graphFibreAtInfinityIso :
    ((graphTriple f E hE).pullback (graphBlowupToBase f E hE)
      (isGoodBlowup_graphBlowupToBase f E hE).isGoodOver.pullbackDefined).D.subscheme ≅
      modificationFibreAtInfinity f (graphBlowupToBase f E hE) :=
  (infinitySection f).kerComapIso (graphBlowupToBase f E hE)

/-- The identification of `graphFibreAtInfinityIso` is compatible with the inclusions into `W`. -/
theorem graphFibreAtInfinityIso_hom_inclusion :
    (graphFibreAtInfinityIso f E hE).hom ≫
        modificationInclusionAtInfinity f (graphBlowupToBase f E hE) =
      ((graphTriple f E hE).pullback (graphBlowupToBase f E hE)
        (isGoodBlowup_graphBlowupToBase f E hE).isGoodOver.pullbackDefined).D.subschemeι :=
  (infinitySection f).kerComapIso_hom_fst (graphBlowupToBase f E hE)

/-- The cohomology sheaves of `Lp^*E` restricted to `p⁻¹(V)` are the pullbacks of those of `E`
restricted to `V`, the projection `p : 𝐏¹_X ⟶ X` being flat. -/
def graphCohomologySheafRestrictIso (V : X.Opens) (n : ℤ) :
    (Scheme.Modules.restrictFunctor
        (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V).ι).obj
        ((DerivedCategory.homologyFunctor (projectiveLineProduct f).Modules n).obj
          ((derivedPullback (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom).obj
            E)) ≅
      (Scheme.Modules.pullback ((pullback.fst f (relativeProjectiveLine S ↘ S)).resLE V
        (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V) le_rfl)).obj
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E)) :=
  haveI : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback
      (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom) :=
    preservesFiniteLimits_modulesPullback_of_flat (pullback.fst f (relativeProjectiveLine S ↘ S))
  haveI : PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback
      (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom) :=
    preservesFiniteColimits_modulesPullback (pullback.fst f (relativeProjectiveLine S ↘ S))
  (Scheme.Modules.restrictFunctor _).mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso
          (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom).app E) ≪≫
        (Functor.mapDerivedCategoryHomologyIso (RingedSpaceModuleAdjunction.modulePullback
          (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom) n).app E) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι _ _).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

/-- Over an open `V ⊆ X` on which all the cohomology sheaves of `E` are finite locally free, all
the cohomology sheaves of `Lp^*E` are finite locally free: `p⁻¹(V)` lies in the locally free
locus of the triple of the graph construction. -/
theorem le_locallyFreeLocus_graphTriple (V : X.Opens)
    (hV : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E))) :
    pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V ≤ (graphTriple f E hE).locallyFreeLocus :=
  (graphTriple f E hE).le_locallyFreeLocus _ fun i =>
    RingedSpace.isFiniteLocallyFreeOver_of_restrict _ _
      (SheafOfModules.IsFiniteLocallyFree.of_iso (graphCohomologySheafRestrictIso f E V i).symm
        (h := SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ (hV i)))

/-- Over an open `V ⊆ X` on which `H^n(E)` is finite locally free of rank `r`, the fibre rank of
`H^n(Lp^*E)` is `r` at every point of `p⁻¹(V)`. -/
theorem fiberRank_cohomologySheaf_graphTriple (V : X.Opens) (n : ℤ) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E)) r]
    {x : projectiveLineProduct f} (hx : x ∈ pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V) :
    Scheme.Modules.fiberRank ((graphTriple f E hE).cohomologySheaf n) x = r := by
  refine (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict
    (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V).ι _ ⟨x, hx⟩).symm.trans ?_
  refine (Scheme.Modules.fiberRank_eq_of_iso (graphCohomologySheafRestrictIso f E V n)
    ⟨x, hx⟩).trans ?_
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    ((pullback.fst f (relativeProjectiveLine S ↘ S)).resLE V
      (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ V) le_rfl)
    ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E)) r
  exact Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank _ r _

open AlgebraicGeometry.ComplexAndDivisorSituation in
/-- For the morphism `b : W ⟶ 𝐏¹_X` of the graph construction and `Q = Lη_ℐ Lb^*Lp^*E`, there is
a closed immersion `t : T ⟶ W_∞` of finite presentation such that
* the cohomology sheaves of `L(t ≫ i_∞)^*Q` are finite locally free,
* (3) every point of `W_∞` lying over an open `V ⊆ X` on which all the cohomology sheaves of `E`
  are finite locally free lies in `T`, and
* (4) at a point of `T` lying over such an open `V`, the rank of `H^n(L(t ≫ i_∞)^*Q)` is the rank
  `r` of `H^n(E)` on `V`. -/
@[stacks 0F90 "clauses (3) and (4)"]
theorem exists_closedImmersion_graphObjectRestrict :
    ∃ (T : Scheme.{u}) (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)),
      IsClosedImmersion t ∧ LocallyOfFinitePresentation t ∧
      ∃ hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((DerivedCategory.homologyFunctor T.Modules n).obj
            ((derivedPullback (t ≫ modificationInclusionAtInfinity f
              (graphBlowupToBase f E hE)).toLRSHom.toShHom).obj (graphObject f E hE))),
        (∀ (w) (V : X.Opens),
          modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∈ V →
          (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            ((Scheme.Modules.pullback V.ι).obj
              ((DerivedCategory.homologyFunctor X.Modules n).obj E))) →
          w ∈ Set.range t) ∧
        ∀ (τ : T) (V : X.Opens) (n : ℤ) (r : ℕ),
          modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∈ V →
          (∀ m : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            ((Scheme.Modules.pullback V.ι).obj
              ((DerivedCategory.homologyFunctor X.Modules m).obj E))) →
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback V.ι).obj
              ((DerivedCategory.homologyFunctor X.Modules n).obj E)) r →
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = r := by
  have hb := isGoodBlowup_graphBlowupToBase f E hE |>.isGoodOver
  obtain ⟨T₀, hT, hfp, -⟩ := ((graphTriple f E hE).pullback _
    hb.pullbackDefined).exists_isGoodChartOpen_ideal_eq_obstructionIdeal hb.isGoodTriple
  have hj : (T₀.subschemeι ≫ (graphFibreAtInfinityIso f E hE).hom) ≫
      modificationInclusionAtInfinity f (graphBlowupToBase f E hE) =
      T₀.subschemeι ≫ ((graphTriple f E hE).pullback _ hb.pullbackDefined).D.subschemeι :=
    (Category.assoc _ _ _).trans
      (congrArg (T₀.subschemeι ≫ ·) (graphFibreAtInfinityIso_hom_inclusion f E hE))
  have hpt : ∀ τ : T₀.subscheme,
      modificationProjectionAtInfinity f (graphBlowupToBase f E hE)
          ((T₀.subschemeι ≫ (graphFibreAtInfinityIso f E hE).hom) τ) =
        pullback.fst f (relativeProjectiveLine S ↘ S) (((T₀.subschemeι ≫
          ((graphTriple f E hE).pullback _ hb.pullbackDefined).D.subschemeι) ≫
            graphBlowupToBase f E hE) τ) := fun τ =>
    congrArg (fun g => pullback.fst f (relativeProjectiveLine S ↘ S)
      ((g ≫ graphBlowupToBase f E hE) τ)) hj
  have := hfp
  refine ⟨T₀.subscheme, T₀.subschemeι ≫ (graphFibreAtInfinityIso f E hE).hom, inferInstance,
    inferInstance, fun n => hj ▸
      (graphTriple f E hE).isFiniteLocallyFree_etaDerivedPullbackRestrictHomology
        hb.isGoodTriple hT n, fun w V hw hV => ?_, fun τ V n r hτ hV hr => ?_⟩
  · have hz : ((graphTriple f E hE).pullback _ hb.pullbackDefined).D.subschemeι
        ((graphFibreAtInfinityIso f E hE).inv w) =
        modificationInclusionAtInfinity f (graphBlowupToBase f E hE) w :=
      congrArg (fun g => g w)
        ((Iso.inv_comp_eq _).mpr (graphFibreAtInfinityIso_hom_inclusion f E hE).symm)
    have h1 : graphBlowupToBase f E hE (((graphTriple f E hE).pullback _
        hb.pullbackDefined).D.subschemeι ((graphFibreAtInfinityIso f E hE).inv w)) ∈
          (graphTriple f E hE).locallyFreeLocus :=
      (congrArg (fun y => graphBlowupToBase f E hE y ∈ (graphTriple f E hE).locallyFreeLocus)
        hz).mpr (le_locallyFreeLocus_graphTriple f E hE V hV hw)
    have hzW : (graphFibreAtInfinityIso f E hE).inv w ∈
        ((graphTriple f E hE).pullback _ hb.pullbackDefined).D.subschemeι ⁻¹ᵁ
          (graphBlowupToBase f E hE ⁻¹ᵁ (graphTriple f E hE).locallyFreeLocus) := h1
    obtain ⟨τ, hτ⟩ := T₀.mem_range_subschemeι_of_comap_eq_bot _
      ((graphTriple f E hE).comap_preimage_locallyFreeLocus_eq_bot hb.isGoodTriple hT) hzW
    refine ⟨τ, ?_⟩
    change (graphFibreAtInfinityIso f E hE).hom (T₀.subschemeι τ) = w
    rw [hτ]
    change ((graphFibreAtInfinityIso f E hE).inv ≫ (graphFibreAtInfinityIso f E hE).hom) w = w
    rw [Iso.inv_hom_id]
    rfl
  · have hτ' := (hpt τ).symm ▸ hτ
    have hx := le_locallyFreeLocus_graphTriple f E hE V hV hτ'
    have hrank :=
      finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf
        (S := graphTriple f E hE) hb.isGoodTriple hT n τ hx
    replace hrank := hrank.trans (fiberRank_cohomologySheaf_graphTriple f E hE V n r hτ')
    refine (@Stacks.Chow.fiberRank_eq_moduleRank _ _ ?_ τ).symm.trans ?_
    refine (congrArg (fun g : T₀.subscheme ⟶ graphBlowup f E hE => Scheme.Modules.fiberRank
      ((DerivedCategory.homologyFunctor T₀.subscheme.Modules n).obj
        ((derivedPullback g.toLRSHom.toShHom).obj (graphObject f E hE))) τ) hj).trans ?_
    exact (@Stacks.Chow.fiberRank_eq_moduleRank _ _
      ((graphTriple f E hE).isFiniteLocallyFree_etaDerivedPullbackRestrictHomology
        hb.isGoodTriple hT n) τ).trans hrank

end Stacks.Chow

end

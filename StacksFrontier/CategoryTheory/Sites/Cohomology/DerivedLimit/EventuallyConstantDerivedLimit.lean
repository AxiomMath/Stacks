module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.LocallyBijectiveHomology
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Cohomology of the derived limit of an eventually constant tower on a site

In the Olsson--Laszlo situation of Stacks 0D6R — a site `C`, a sheaf of rings `O`, a weak Serre
subcategory `A` of `O`-modules, and a class `B` of objects covering every object of `C`, each
`V ∈ B` carrying an integer bound `d_V` and a cofinal system of coverings on whose members the
cohomology of every module of `A` vanishes above `d_V` — let `(Kₙ)` be an inverse system in
`D⁺_A(O)` whose cohomology systems `(Hʲ(Kₙ))` are eventually constant with values `ℋʲ`. Then
the cohomology of a derived inverse limit of `(Kₙ)` is `ℋʲ`:

`Hʲ(R lim Kₙ) = ℋʲ`.

## Main definitions

* `Stacks.Cohomology.cohomologyToEventuallyConstantValue`: the canonical map from the degree-`j`
  cohomology of a presented derived limit to the eventual value of the degree-`j` cohomology
  tower.

## Main results

* `Stacks.Cohomology.isIso_cohomologyToEventuallyConstantValue` (Stacks 0D6T): that map is an
  isomorphism, in every degree.

## Implementation notes

The tower is represented by a tower of complexes of injectives, so that the derived limit becomes
the mapping cocone of a Milnor difference of complexes; the bound `d_V` makes the derived
sections over a member of a distinguished covering of a basis object stabilise in the two
degrees `j - 1, j` that control `Hʲ`; and a map of complexes of sheaves of modules which is a
homology isomorphism after evaluating on a cofinal system of coverings of a locally covering
class of objects is a homology isomorphism.

Eventual constancy with a specified value is `Stacks.InverseSystem.EventuallyConstantValue`,
which carries the stabilising index and the identification of that stage with the value. This is
what lets the conclusion be about the canonical comparison map rather than about the existence
of an abstract isomorphism.

Membership in `D⁺_A(O)` is `Stacks.DerivedCategoryB.derivedCategoryBPlus`, applied pointwise to
the tower; the derived limit is supplied by its defining distinguished triangle, in the shape
Stacks 0A09 produces it, so that its projection to each stage — and hence the comparison map —
is the canonical one.

The value `ℋʲ` is not assumed to lie in `A`; it does automatically, being isomorphic to
`Hʲ(K_N)` for large `N`.

## References

* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.InverseSystem

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology

universe v u wRing wModule

/-- Evaluating a sheaf of modules on an object of the site is an additive functor, so its right
derived functors exist; this is what `Stacks.Cohomology.moduleCohomology` of Stacks 0D6R is
built from. -/
private noncomputable local instance evaluation_additive
    (S : OlssonLaszloSituation.{v, u, wRing, wModule}) (U : S.Cᵒᵖ) :
    (SheafOfModules.evaluation S.O U).Additive where
  map_add := rfl

/-- **A finite window of cohomology isomorphisms is seen by the cohomology over a member of a
distinguished covering.** In the Olsson--Laszlo situation, over a member of a covering in the
cofinal system attached to a basis object `V`, the right derived functor of evaluation has
cohomological dimension `S.degreeBound V hV` on the weak Serre subcategory `S.A`; so a map in
`D⁺` whose cohomology maps are invertible in the window `[j - d - 2, j + 1]` induces an
isomorphism on degree-`j` cohomology after that functor. -/
private theorem isIso_rightDerivedEvaluation_map_of_window
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (V : S.C) (hV : S.B V) (𝒰 : PreZeroHypercover.{max u v} V)
    (h𝒰 : (S.coverings V hV).cov 𝒰) (i : 𝒰.I₀)
    {K L : DerivedCategory.Plus (SheafOfModules.{wModule} S.O)}
    (hK : ∀ q, S.A ((DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (hL : ∀ q, S.A ((DerivedCategory.Plus.homologyFunctor _ q).obj L))
    (f : K ⟶ L) (j : ℤ)
    (hwindow : ∀ q : ℤ, j - S.degreeBound V hV - 2 ≤ q → q ≤ j + 1 →
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map f)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{wModule} (S.O.obj.obj (.op (𝒰.X i)))) j).map
      ((SheafOfModules.evaluation S.O (.op (𝒰.X i))).rightDerivedFunctorPlus.map f)) := by
  let E := SheafOfModules.evaluation S.O (.op (𝒰.X i))
  have htri := Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus E
  let G := E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have : G.IsTriangulated := by dsimp [G]; infer_instance
  apply BoundedCohomologicalDimension.isIso_homology_map_of_isIso_window G S.A
    (WeakSerre.isWeakSerre_of_isWeakSerreClass S.A) (S.degreeBound V hV) _ _ hK hL f j hwindow
  · intro q M hM
    exact BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single E M
      (S.degreeBound V hV) q (fun p hp => S.vanishing V hV 𝒰 h𝒰 i p hp M hM)
  · intro X a ha
    have : (E.rightDerivedFunctorPlus.obj X).IsGE a :=
      CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj E X a
    change (DerivedCategory.Plus.ι.obj (E.rightDerivedFunctorPlus.obj X)).IsGE a
    infer_instance

/-- **One stage of an eventually constant tower works uniformly over a basis object.** For a
tower in `D⁺` with cohomology in `S.A` whose cohomology systems are eventually constant, and a
basis object `V`, there is a single index `N` past which the transition maps become isomorphisms
on the degree-`j - 1` and degree-`j` cohomology of the derived sections over every member of
every distinguished covering of `V`.

The index comes from the finite window of degrees `[j - d_V - 3, j + 1]` inspected by
`isIso_rightDerivedEvaluation_map_of_window`. -/
private theorem exists_eventual_stage_rightDerived_evaluation
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (K : ℕᵒᵖ ⥤ DerivedCategory.Plus (SheafOfModules.{wModule} S.O))
    (hK : ∀ (n : ℕ) (q : ℤ), S.A ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (K.obj (.op n))))
    (ℋ : ℤ → SheafOfModules.{wModule} S.O)
    (e : ∀ j : ℤ, EventuallyConstantValue (K ⋙ DerivedCategory.Plus.homologyFunctor _ j) (ℋ j))
    (V : S.C) (hV : S.B V) (j : ℤ) :
    ∃ N : ℕ, ∀ (𝒰 : PreZeroHypercover.{max u v} V), (S.coverings V hV).cov 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ) (hn : N ≤ n) (r : ℤ), r = j - 1 ∨ r = j →
        IsIso ((K ⋙ (SheafOfModules.evaluation S.O (.op (𝒰.X i))).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ r).map (homOfLE hn).op) := by
  obtain ⟨N, hN⟩ := exists_common_stage_window
    (fun q => K ⋙ DerivedCategory.Plus.homologyFunctor _ q) ℋ e j
    (S.degreeBound V hV + 1)
  refine ⟨N, fun 𝒰 h𝒰 i n hn r hr => ?_⟩
  apply isIso_rightDerivedEvaluation_map_of_window S V hV 𝒰 h𝒰 i
    (hK n) (hK N) (K.map (homOfLE hn).op) r
  intro q hq₁ hq₂
  rcases hr with rfl | rfl <;>
    exact (e q).isEventuallyConstant.isIso_map (homOfLE hn).op
      (homOfLE (hN q (by omega) (by omega)).1).op

/-- **The projection of the mapping cocone onto a stabilising stage is a homology isomorphism
of sheaves.** Given a tower `I` of complexes of sheaves of modules whose degree-`j` homology
tower is constant past `n₀`, and whose derived sections over the members of distinguished
coverings stabilise in degrees `j - 1, j`, the projection of the mapping cocone of the Milnor
difference of `I` onto the stage `n₀` is an isomorphism on degree-`j` homology.

By `Stacks.Cohomology.isIso_homologyMap_iff_w` the conclusion is local bijectivity of a map of
presheaves, and over a basis object the map is factored as the projection to a late stage
followed by a transition map of the tower, which is already a homology isomorphism. -/
private theorem isIso_sheaf_homology_cocone_projection
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    [HasProductsOfShape ℕ (SheafOfModules.{wModule} S.O)]
    (I : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{wModule} S.O) ℤ)
    (j : ℤ) (n₀ : ℕ)
    (htail : (I ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) j).IsEventuallyConstantTo
      (.op n₀))
    (hlocal : ∀ V (hV : S.B V), ∃ N : ℕ,
      ∀ (𝒰 : PreZeroHypercover.{max u v} V), (S.coverings V hV).cov 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ) (hn : N ≤ n) (r : ℤ), r = j - 1 ∨ r = j →
        IsIso (((I ⋙ (SheafOfModules.evaluation S.O (.op (𝒰.X i))).mapHomologicalComplex
          (.up ℤ)) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) r).map
          (homOfLE hn).op)) :
    let X := fun n : ℕ => I.obj (.op n)
    let d := Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
      I.map (homOfLE (Nat.le_succ n)).op)
    IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map
      ((CochainComplex.mappingCocone.triangle d).mor₁ ≫ Pi.π X n₀)) := by
  intro X d
  let := HasDerivedCategory.standard (PresheafOfModules.{wModule} S.O.obj)
  let p := (CochainComplex.mappingCocone.triangle d).mor₁
  let H := (SheafOfModules.forget S.O).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor (PresheafOfModules.{wModule} S.O.obj) (.up ℤ) j ⋙
    PresheafOfModules.toPresheaf S.O.obj
  apply (isIso_homologyMap_iff_w S.O _ j).2
  apply w_of_cofinal_local_isomorphisms S.J S.B S.basis_cover S.coverings
    (H.map (p ≫ Pi.π X n₀))
  intro V hV
  obtain ⟨N, hN⟩ := hlocal V hV
  let N' := max N n₀
  let t := I.map (homOfLE (show n₀ ≤ N' from le_max_right _ _)).op
  refine ⟨H.obj (I.obj (.op N')), H.map (p ≫ Pi.π X N'), H.map t, ?_, ?_, ?_⟩
  · exact map_mappingCocone_proj_comp_map (SheafOfModules.forget S.O)
      (PresheafOfModules.toPresheaf S.O.obj) I j n₀ N' (le_max_right _ _)
  · exact (isIso_homologyMap_iff_w S.O t j).1 (htail _)
  · intro 𝒰 h𝒰 i
    let := HasDerivedCategory.standard (ModuleCat.{wModule} (S.O.obj.obj (.op (𝒰.X i))))
    apply isIso_presheaf_homologyMap_app_of_evaluation S.O _ j
    apply isIso_homologyMap_mappingCocone_proj
      (SheafOfModules.evaluation S.O (.op (𝒰.X i))) I j N'
    intro n hn r hr
    let F := (I ⋙ (SheafOfModules.evaluation S.O (.op (𝒰.X i))).mapHomologicalComplex
      (.up ℤ)) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) r
    have hF : F.IsEventuallyConstantTo (.op N) := by
      intro n f
      exact hN 𝒰 h𝒰 i n.unop (leOfHom f.unop) r hr
    exact hF.isIso_map (homOfLE hn).op (homOfLE (show N ≤ N' from le_max_left _ _)).op

/-- **The canonical comparison from the cohomology of a presented derived limit to the
eventual value of the cohomology tower.** It is the map on degree-`j` cohomology induced by the
projection of the derived limit onto the stabilising stage, followed by the chosen
identification of that stage with the value. -/
noncomputable def cohomologyToEventuallyConstantValue
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{wModule} S.O))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} S.O))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) (j : ℤ)
    (ℋ : SheafOfModules.{wModule} S.O)
    (e : EventuallyConstantValue
      (K ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j) ℋ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j).obj L ⟶ ℋ :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j).map
      (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) e.index) ≫
    e.iso.hom

/-- **Stacks Project, Tag 0D6T.** If an inverse system in `D^+_A` has eventually
constant cohomology sheaves with values `ℋʲ`, then the canonical map from the cohomology
of any presented derived inverse limit to `ℋʲ` is an isomorphism, for every `j`. -/
@[stacks 0D6T]
theorem isIso_cohomologyToEventuallyConstantValue
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : ∀ n : ℕ, DerivedCategoryB.derivedCategoryBPlus S.A (K.obj ⟨n⟩))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} S.O))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} S.O)))
    (ℋ : ℤ → SheafOfModules.{wModule} S.O)
    (e : ∀ j : ℤ, EventuallyConstantValue
      (K ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j) (ℋ j)) :
    ∀ j : ℤ, IsIso (cohomologyToEventuallyConstantValue S K L p j (ℋ j) (e j)) := by
  let A := SheafOfModules.{wModule} S.O
  have : HasProductsOfShape ℕ A :=
    SheafOfModules.hasLimitsOfShape.{wModule} (R := S.O) (Discrete ℕ)
  let Kp : ℕᵒᵖ ⥤ DerivedCategory.Plus A :=
    DerivedCategory.TStructure.t.plus.lift K (fun n => by
      obtain ⟨a, ha⟩ := (hK n.unop).1
      exact ⟨a, (DerivedCategory.isGE_iff _ _).2 ha⟩)
  have hKp (n : ℕ) (q : ℤ) :
      S.A ((DerivedCategory.Plus.homologyFunctor A q).obj (Kp.obj (.op n))) :=
    (hK n).2 q
  have ep (q : ℤ) : EventuallyConstantValue
      (Kp ⋙ DerivedCategory.Plus.homologyFunctor A q) (ℋ q) := e q
  obtain ⟨I, hI, hKI, ⟨eI⟩⟩ := exists_injective_tower_representative Kp
  obtain ⟨δ, hδ⟩ := hL
  let Ic := I ⋙ CochainComplex.Plus.ι A
  let eIc : Ic ⋙ DerivedCategory.Q ≅ K :=
    Functor.isoWhiskerRight eI DerivedCategory.Plus.ι
  obtain ⟨a, ha⟩ := exists_mappingCocone_iso_of_isKInjective_tower Ic hKI K eIc L p δ hδ
  intro j
  let H := DerivedCategory.homologyFunctor A j
  let hc : Ic ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) j ≅ K ⋙ H :=
    Functor.isoWhiskerLeft Ic (DerivedCategory.homologyFunctorFactors A j).symm ≪≫
      Functor.isoWhiskerRight eIc H
  have htail : (Ic ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) j).IsEventuallyConstantTo
      (.op (e j).index) := by
    intro n f
    exact (NatIso.isIso_map_iff hc f).2 ((e j).isEventuallyConstant f)
  have hlocal : ∀ V (hV : S.B V), ∃ N : ℕ,
      ∀ (𝒰 : PreZeroHypercover.{max u v} V), (S.coverings V hV).cov 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ) (hn : N ≤ n) (r : ℤ), r = j - 1 ∨ r = j →
        IsIso (((Ic ⋙ (SheafOfModules.evaluation S.O (.op (𝒰.X i))).mapHomologicalComplex
          (.up ℤ)) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) r).map
          (homOfLE hn).op) := by
    intro V hV
    obtain ⟨N, hN⟩ := exists_eventual_stage_rightDerived_evaluation S Kp hKp ℋ ep V hV j
    refine ⟨N, fun 𝒰 h𝒰 i n hn r hr => ?_⟩
    let E := SheafOfModules.evaluation S.O (.op (𝒰.X i))
    exact isIso_homologyMap_of_isIso_rightDerivedFunctorPlus_map E (hI n) (hI N)
      (I.map (homOfLE hn).op) r <| (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight eI (E.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ r)) (homOfLE hn).op).2
      (hN 𝒰 h𝒰 i n hn r hr)
  have hraw := isIso_sheaf_homology_cocone_projection S Ic j (e j).index htail hlocal
  let X := fun n : ℕ => Ic.obj (.op n)
  let d := Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
    Ic.map (homOfLE (Nat.le_succ n)).op)
  let f := (CochainComplex.mappingCocone.triangle d).mor₁ ≫ Pi.π X (e j).index
  have hf : IsIso (H.map (DerivedCategory.Q.map f)) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A j) f).2 hraw
  have heq : H.map (DerivedCategory.Q.map f) ≫ H.map (eIc.hom.app (.op (e j).index)) =
      H.map a.hom ≫ H.map (p ≫ Pi.π (fun n : ℕ => K.obj (.op n)) (e j).index) :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (ha (e j).index)).trans (H.map_comp _ _))
  have hcomp : IsIso (H.map a.hom ≫
      H.map (p ≫ Pi.π (fun n : ℕ => K.obj (.op n)) (e j).index)) := by
    rw [← heq]
    exact IsIso.comp_isIso' hf inferInstance
  have hproj : IsIso (H.map (p ≫ Pi.π (fun n : ℕ => K.obj (.op n)) (e j).index)) :=
    IsIso.of_isIso_comp_left (H.map a.hom) _
  dsimp only [cohomologyToEventuallyConstantValue]
  exact inferInstanceAs (IsIso (H.map (p ≫ Pi.π (fun n : ℕ => K.obj (.op n)) (e j).index) ≫
    (e j).iso.hom))

end Stacks.Cohomology

end

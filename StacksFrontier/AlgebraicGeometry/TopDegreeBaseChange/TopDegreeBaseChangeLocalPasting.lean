module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyCompositionFunctoriality
public import StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal

/-!
# The two-step composite of [Stacks, Tag 0EX3] (c) for pasted squares

The canonical map of conclusion (c) of [Stacks, Tag 0EX3] is `Hᵈ` of the composite

> `φ : Lh^* Rf'_*(F'[0]) ⟶ Rf''_* L(h')^*(F'[0]) ⟶ Rf''_*((h')^* F'[0])`

of the derived base change map of [Stacks, Tag 08HY] and `Rf''_*` of the comparison from derived
to ordinary pullback. The source checks (c) *"locally on `Y'` and `Y''`"*, and doing so means
pasting the square with open-immersion squares on either side. This file proves the pasting law
for `φ` and its consequences for invertibility, for morphisms of ringed spaces and with nothing
assumed about the modules.

## Main results

* `…derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle`:
  the comparison from derived to ordinary pullback is compatible with the composition
  isomorphisms of [Stacks, Tag 0D5S] and of ordinary pullback.
* `…TopDegreeBaseChange.derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_hpaste`:
  **`φ` of a horizontally pasted rectangle** is `φ` of the right-hand square pulled back, followed
  by `φ` of the left-hand square, up to the composition isomorphisms. The derived half is
  [Stacks, Tag 0ATM].
* `…isIso_derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_of_isOpenImmersions`:
  `φ` is invertible for a cartesian square along open immersions.
* `…TopDegreeBaseChange.isIso_homologyFunctor_map_derivedPullback_map_iff_of_isOpenImmersions_left`
  and `…TopDegreeBaseChange.isIso_homologyFunctor_map_iff_of_isOpenImmersions_right`: pasting an
  open-immersion square on either side does not change whether `Hᵈ(φ)` is invertible.

## Implementation notes

*The rearrangements are proved at variables.* Each identity is assembled by
`comp_eq_of_six` or `comp_eq_of_three` from facts stated about the factors, which are then
supplied in argument position. Rewriting directly in the goal fails: the components of the
derived-pullback comparison have declared targets that are only definitionally equal to the
spellings of their neighbours, and the matcher times out on them.

*The derived-category instance.* This file is kept apart from `TopDegreeBaseChangeLocal.lean`
because its statements must be elaborated under `HasDerivedCategory.standard` at default
priority, as [Stacks, Tag 0ATM] is: under the import closure of the scheme-level file a second
`HasDerivedCategory` instance is found first at default priority, and raising the priority of the
standard one makes the identification with the statement of Tag 0ATM time out.

No `@[stacks 0EX3]` attribute is placed: these are steps of the reduction of (c) to affine bases.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open DerivedCategory

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

section Homotopy

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} [F.Additive] [G.Additive] [H.Additive]

/-- On cochain complexes, the composition isomorphism `F ⋙ G ≅ H` induced degreewise, at the
complex `M[0]`, followed by the comparison `H(M[0]) ≅ (H M)[0]`, is the comparison for `F ⋙ G`
followed by `e` placed in degree `0`. -/
theorem mapHomologicalComplexCompIso_hom_app_single_comp (e : F ⋙ G ≅ H) (M : C₁) :
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor C₁ 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (ComplexShape.up ℤ) 0).hom.app M ≫
      (CochainComplex.singleFunctor C₃ 0).map (e.hom.app M) := by
  ext i
  by_cases h : i = 0
  · subst h
    have h0 : ((CochainComplex.singleFunctor C₃ 0).map (e.hom.app M)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj (F.obj M))).hom ≫
          e.hom.app M ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (H.obj M)).inv :=
      HomologicalComplex.single_map_f_self _ 0 _
    simp only [Functor.mapHomologicalComplexCompIso] at *
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Functor.comp_map, h0,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_right_assoc]
    exact (e.hom.naturality _).symm
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ h]

/-- **`Functor.mapHomotopyCategorySingleFunctor` against a composition isomorphism.** In the
homotopy category, the composition isomorphism induced by `e : F ⋙ G ≅ H` at `M[0]`, followed by
the comparison `H(M[0]) ≅ (H M)[0]`, is `G` of the comparison for `F`, the comparison for `G`, and
`e` placed in degree `0`. -/
theorem mapHomotopyCategoryCompIso_hom_app_single_comp (e : F ⋙ G ≅ H) (M : C₁) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor C₁ 0).obj M) ≫
      (H.mapHomotopyCategorySingleFunctor 0).hom.app M =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategorySingleFunctor 0).hom.app M) ≫
      (G.mapHomotopyCategorySingleFunctor 0).hom.app (F.obj M) ≫
      (HomotopyCategory.singleFunctor C₃ 0).map (e.hom.app M) := by
  rw [reassoc_of%
      (Stacks.Cohomology.ModulePushforwardComparison.mapHomotopyCategorySingleFunctor_hom_app_comp
        F G M),
    Stacks.Cohomology.ModulePushforwardComparison.mapHomotopyCategorySingleFunctor_hom_app
      (F ⋙ G) M,
    Stacks.Cohomology.ModulePushforwardComparison.mapHomotopyCategorySingleFunctor_hom_app H M]
  have hq := Functor.mapHomotopyCategoryCompIso_hom_app_quotient e
    ((CochainComplex.singleFunctor C₁ 0).obj M)
  have hs : (HomotopyCategory.singleFunctor C₃ 0).map (e.hom.app M) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor C₃ 0).map (e.hom.app M)) := rfl
  refine (congrArg (· ≫ _) hq).trans ?_
  rw [hs]
  exact ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (mapHomologicalComplexCompIso_hom_app_single_comp e M))).trans
    (Functor.map_comp _ _ _)

end Homotopy


section Abstract

variable {𝒞 : Type*} [Category* 𝒞]

/-- The rearrangement behind
`derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle`, at variables:
six identities between the factors combine to the asserted one. -/
theorem comp_eq_of_six {A₁ A₂ A₃ A₄ A₅ A₆ B₂ B₃ B₄ B₅ B₆ B₇ B₈ B₉ : 𝒞}
    (i : A₁ ⟶ A₂) (ps : A₂ ⟶ A₃) (cab : A₃ ⟶ A₄) (qt : A₄ ⟶ A₅) (sinv : A₅ ⟶ A₆)
    (pps : A₁ ⟶ B₂) (i' : B₂ ⟶ A₃) (pcb : B₂ ⟶ B₃) (ca' : B₃ ⟶ B₄) (qpb : B₄ ⟶ A₄)
    (pqtb : B₃ ⟶ B₅) (psinv : B₅ ⟶ B₆) (pshom : B₆ ⟶ B₅) (ca : B₅ ⟶ B₇)
    (qatb : B₄ ⟶ B₇) (qta : B₇ ⟶ B₈) (qe : B₈ ⟶ A₅) (sinv' : B₈ ⟶ B₉) (se : B₉ ⟶ A₆)
    (hI : pps ≫ i' = i ≫ ps) (hcoh : i' ≫ cab = pcb ≫ ca' ≫ qpb)
    (hc : psinv ≫ pshom = 𝟙 _) (hC : pqtb ≫ ca = ca' ≫ qatb)
    (hkey : qpb ≫ qt = qatb ≫ qta ≫ qe) (hS : qe ≫ sinv = sinv' ≫ se) :
    i ≫ ps ≫ cab ≫ qt ≫ sinv =
      pps ≫ pcb ≫ pqtb ≫ psinv ≫ pshom ≫ ca ≫ qta ≫ sinv' ≫ se := by
  rw [reassoc_of% hc, reassoc_of% hC, ← reassoc_of% hI, reassoc_of% hcoh, reassoc_of% hkey, hS]

/-- The rearrangement behind `derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_hpaste`,
at variables. -/
theorem comp_eq_of_three {A₁ A₂ A₃ A₄ A₅ A₆ A₇ B₁ B₂ : 𝒞}
    (ci : A₁ ⟶ A₂) (lb : A₂ ⟶ A₃) (lr : A₃ ⟶ A₄) (bc2 : A₄ ⟶ A₅) (rd : A₅ ⟶ A₆)
    (rs : A₆ ⟶ A₇) (bc2' : A₃ ⟶ B₁) (rlg : B₁ ⟶ A₅) (rch : B₁ ⟶ B₂) (bcR : A₁ ⟶ B₂)
    (rdR : B₂ ⟶ A₇)
    (h0 : ci ≫ lb ≫ bc2' ≫ rch = bcR) (hn : lr ≫ bc2 = bc2' ≫ rlg)
    (h1 : rch ≫ rdR = rlg ≫ rd ≫ rs) :
    ci ≫ lb ≫ lr ≫ bc2 ≫ rd ≫ rs = bcR ≫ rdR := by
  rw [← h0, Category.assoc, Category.assoc, Category.assoc, h1, reassoc_of% hn]

end Abstract

section DerivedToOrdinary

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

variable {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The comparison from derived to ordinary pullback is compatible with composition.** The
composition isomorphism `Lb^* ⋙ La^* ≅ L(a ≫ b)^*` of [Stacks, Tag 0D5S] at `M[0]`, followed by
the comparison `L(a ≫ b)^*(M[0]) ⟶ ((a ≫ b)^* M)[0]`, is `La^*` of the comparison for `b`, the
comparison for `a`, and the ordinary composition isomorphism `a^* b^* M ≅ (a ≫ b)^* M` placed in
degree `0` (here in its inverse direction). -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (derivedPullbackCompIsoCanonical a b).hom.app
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).obj M) ≫
      derivedToOrdinaryPullbackSingle (a ≫ b) M 0 =
    (derivedPullback a).map (derivedToOrdinaryPullbackSingle b M 0) ≫
      derivedToOrdinaryPullbackSingle a ((modulePullback b).obj M) 0 ≫
      (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M) := by
  have hcoh :=
    Cohomology.DerivedPushforwardComposition.derivedPullbackCompIsoCanonical_hom_app_comp_comparison
      a b ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).obj M)
  have hnatI := (derivedPullbackCompIsoCanonical a b).hom.naturality
    ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Z)) 0).hom.app M)
  have hnatC := (derivedPullbackComparison a).naturality
    ((Functor.mapHomotopyCategorySingleFunctor (modulePullback b) 0).hom.app M)
  have hkey : Qh.map ((pullbackOnHomotopyCompIso a b).hom.app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).obj M)) ≫
      Qh.map (((modulePullback (a ≫ b)).mapHomotopyCategorySingleFunctor 0).hom.app M) =
    Qh.map (((modulePullback a).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePullback b).mapHomotopyCategorySingleFunctor 0).hom.app M)) ≫
      Qh.map (((modulePullback a).mapHomotopyCategorySingleFunctor 0).hom.app
        ((modulePullback b).obj M)) ≫
      Qh.map ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg Qh.map (mapHomotopyCategoryCompIso_hom_app_single_comp
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b) M)
  have hnatS :=
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) 0).inv.naturality
      ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom.app M)
  have hc : (derivedPullback a).map
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0).inv.app
          ((modulePullback b).obj M)) ≫
      (derivedPullback a).map
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app
          ((modulePullback b).obj M)) = 𝟙 _ :=
    ((derivedPullback a).mapIso (((singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) 0).app
        ((modulePullback b).obj M)).symm)).hom_inv_id
  unfold derivedToOrdinaryPullbackSingle
  simp only [Functor.map_comp, Category.assoc]
  exact comp_eq_of_six _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnatI hcoh hc hnatC hkey hnatS

end DerivedToOrdinary

section Pasting

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.DerivedPullback.Composition

variable {X'' X' X Y'' Y' Y : RingedSpace.{u, u}} (g' : X'' ⟶ X') (g : X' ⟶ X)
  (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

/-- **The two-step composite of [Stacks, Tag 0EX3] (c) for horizontally pasted squares.** For two
horizontally composable commutative squares of ringed spaces and a module `M` on `X`, write
`φ(M) : Lh^* Rf_*(M[0]) ⟶ Rf'_*(g^* M[0])` for the derived base change map of [Stacks, Tag 08HY]
followed by `Rf'_*` of the comparison from derived to ordinary pullback, as in the source's
definition of `γ`. Then `φ` of the outer rectangle is the inverse composition isomorphism of
[Stacks, Tag 0D5S], `Lh'^*` of `φ` of the right-hand square, `φ` of the left-hand square at
`g^* M`, and `Rf''_*` of the ordinary composition isomorphism `g'^* g^* M ≅ (g' ≫ g)^* M`.

The derived half is [Stacks, Tag 0ATM]; the ordinary half is
`derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle`; the naturality of
the base change map of the left-hand square joins them. -/
theorem derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_hpaste
    (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedPullbackCompIsoCanonical h' h).inv.app
        ((derivedPushforward f).obj ((singleFunctor _ 0).obj M)) ≫
      (derivedPullback h').map
        (derivedBaseChangeMap g f' f h sq₁ ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f').map (derivedToOrdinaryPullbackSingle g M 0)) ≫
      (derivedBaseChangeMap g' f'' f' h' sq₂ ((singleFunctor _ 0).obj ((modulePullback g).obj M)) ≫
        (derivedPushforward f'').map
          (derivedToOrdinaryPullbackSingle g' ((modulePullback g).obj M) 0)) ≫
      (derivedPushforward f'').map ((singleFunctor _ 0).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp g' g).hom.app M)) =
    derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h) (hcomp_square g' g f'' f' f h' h sq₁ sq₂)
        ((singleFunctor _ 0).obj M) ≫
      (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle (g' ≫ g) M 0) := by
  have h0 := derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂
    ((singleFunctor _ 0).obj M)
  have hn := derivedBaseChangeMap_naturality g' f'' f' h' sq₂
    (derivedToOrdinaryPullbackSingle g M 0)
  have h1 : (derivedPushforward f'').map
        ((derivedPullbackCompIsoCanonical g' g).hom.app ((singleFunctor _ 0).obj M)) ≫
      (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle (g' ≫ g) M 0) =
    (derivedPushforward f'').map
        ((derivedPullback g').map (derivedToOrdinaryPullbackSingle g M 0)) ≫
      (derivedPushforward f'').map
        (derivedToOrdinaryPullbackSingle g' ((modulePullback g).obj M) 0) ≫
      (derivedPushforward f'').map ((singleFunctor _ 0).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp g' g).hom.app M)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _
      (derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle g' g M)
  rw [Functor.map_comp]
  simp only [Category.assoc]
  exact comp_eq_of_three _ _ _ _ _ _ _ _ _ _ _ h0 hn h1

/-- **The two-step composite is invertible for a cartesian square along open immersions.** Both
factors are: the derived base change map by
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`, and the
comparison from derived to ordinary pullback because the derived pullback along an open
immersion is not derived (`isIso_derivedPullbackComparison_of_isOpenImmersion`). -/
theorem isIso_derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_of_isOpenImmersions
    [SheafedSpace.IsOpenImmersion g] [SheafedSpace.IsOpenImmersion h]
    (sq : IsPullback g f' f h) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (derivedBaseChangeMap g f' f h sq.w ((singleFunctor _ 0).obj M) ≫
      (derivedPushforward f').map (derivedToOrdinaryPullbackSingle g M 0)) := by
  have hb := isIso_derivedBaseChangeMap_of_isOpenImmersions g f' f h sq ((singleFunctor _ 0).obj M)
  have hc : IsIso (derivedPullbackComparison g) :=
    isIso_derivedPullbackComparison_of_isOpenImmersion g
  have hd : IsIso (derivedToOrdinaryPullbackSingle g M 0) := by
    unfold derivedToOrdinaryPullbackSingle
    infer_instance
  infer_instance

/-- **The pasting of `φ` with an open-immersion square on the left.** If the left-hand square is
a cartesian square of open immersions, `Hᵈ` of `Lh'^*` of `φ` of the right-hand square is
invertible exactly when `Hᵈ` of `φ` of the rectangle is. -/
theorem isIso_homologyFunctor_map_derivedPullback_map_iff_of_isOpenImmersions_left
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion h']
    (sq₁ : g ≫ f = f' ≫ h) (sq₂ : IsPullback g' f'' f' h')
    (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ) :
    IsIso ((homologyFunctor _ d).map ((derivedPullback h').map
        (derivedBaseChangeMap g f' f h sq₁ ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f').map (derivedToOrdinaryPullbackSingle g M 0)))) ↔
      IsIso ((homologyFunctor _ d).map
        (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
            (hcomp_square g' g f'' f' f h' h sq₁ sq₂.w) ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle (g' ≫ g) M 0))) := by
  have := isIso_derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_of_isOpenImmersions
    g' f'' f' h' sq₂ ((modulePullback g).obj M)
  rw [← derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_hpaste g' g f'' f' f h' h
    sq₁ sq₂.w M]
  conv_rhs => rw [(homologyFunctor _ d).map_comp, (homologyFunctor _ d).map_comp,
    (homologyFunctor _ d).map_comp, isIso_comp_left_iff, ← Category.assoc,
    isIso_comp_right_iff, isIso_comp_right_iff]

/-- **The pasting of `φ` with an open-immersion square on the right.** If the right-hand square
is a cartesian square of open immersions, `Hᵈ` of `φ` of the left-hand square at `g^* M` is
invertible exactly when `Hᵈ` of `φ` of the rectangle is. -/
theorem isIso_homologyFunctor_map_iff_of_isOpenImmersions_right
    [SheafedSpace.IsOpenImmersion g] [SheafedSpace.IsOpenImmersion h]
    (sq₁ : IsPullback g f' f h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ) :
    IsIso ((homologyFunctor _ d).map
        (derivedBaseChangeMap g' f'' f' h' sq₂
            ((singleFunctor _ 0).obj ((modulePullback g).obj M)) ≫
          (derivedPushforward f'').map
            (derivedToOrdinaryPullbackSingle g' ((modulePullback g).obj M) 0))) ↔
      IsIso ((homologyFunctor _ d).map
        (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
            (hcomp_square g' g f'' f' f h' h sq₁.w sq₂) ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle (g' ≫ g) M 0))) := by
  have := isIso_derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_of_isOpenImmersions
    g f' f h sq₁ M
  rw [← derivedBaseChangeMap_comp_derivedToOrdinaryPullbackSingle_hpaste g' g f'' f' f h' h
    sq₁.w sq₂ M]
  conv_rhs => rw [(homologyFunctor _ d).map_comp, (homologyFunctor _ d).map_comp,
    (homologyFunctor _ d).map_comp, isIso_comp_left_iff, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- `Hᵈ` of the two-step composite depends on the horizontal arrows of the square only through
their values: it may be transported along equalities of them. -/
theorem isIso_homologyFunctor_map_derivedBaseChangeMap_comp_congr {g₁ g₂ : X'' ⟶ X}
    {h₁ h₂ : Y'' ⟶ Y} (eg : g₁ = g₂) (eh : h₁ = h₂) (sq₁ : g₁ ≫ f = f'' ≫ h₁)
    (sq₂ : g₂ ≫ f = f'' ≫ h₂) (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ) :
    IsIso ((homologyFunctor _ d).map
        (derivedBaseChangeMap g₁ f'' f h₁ sq₁ ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle g₁ M 0))) ↔
      IsIso ((homologyFunctor _ d).map
        (derivedBaseChangeMap g₂ f'' f h₂ sq₂ ((singleFunctor _ 0).obj M) ≫
          (derivedPushforward f'').map (derivedToOrdinaryPullbackSingle g₂ M 0))) := by
  subst eg eh
  rfl

end Pasting

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

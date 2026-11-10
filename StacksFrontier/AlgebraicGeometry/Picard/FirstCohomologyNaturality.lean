module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicardSequence
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Naturality of the Picard-group identification in a morphism of schemes

[Stacks, Tag 09NU] identifies the first cohomology of the sheaf of units of a ringed space with
its Picard group, one space at a time.  This file proves that identification natural in a
morphism of schemes `f : X' ⟶ X`: the square

`H¹(X, 𝒪_X^*) ⟶ H¹(X, f_*𝒪_{X'}^*) ⟶ H¹(X', 𝒪_{X'}^*)`, `Pic(X) ⟶ Pic(X')`,

whose horizontal maps are the map induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*` followed by the first Leray
edge map of [Stacks, Tag 01F2] and pullback of Picard classes, commutes.

The route is through Čech transition cocycles, which is what pins down the torsor
classification of [Stacks, Tag 02FQ].  Three ingredients go into it.  The first is
cohomological: the first Leray edge map `H¹(X, f_*G) ⟶ H¹(X', G)` carries the Čech class of a
cocycle of `f_*G` on a cover of `X` to the Čech class of the same cocycle read on any cover of
`X'` refining the preimage cover.  The second is the transition cocycle of a torsor of generators:
the difference of two generators of an invertible module is their transition unit.  The third
combines them: the pullbacks of a family of local generators of `L` have, as transition
cocycle, the transition cocycle of the original generators pushed along
`𝒪_X^* ⟶ f_*𝒪_{X'}^*`.

## Main definitions

* `Stacks.Picard.FirstCohomology.cochainPullback` — a Čech cochain of a direct image, read on a
  cover of the source refining the preimage cover.
* `Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard` — the identification of Tag 09NU over
  `Stacks.Picard.ofScheme`.
* `Stacks.Picard.FirstCohomology.h1NativeUnitsPullback` — pullback on native first cohomology of
  the sheaf of units.

## Main results

* `Stacks.Picard.FirstCohomology.abelianEdgeMap_cechH1ToRightDerivedSections` — the first Leray
  edge map on Čech classes.
* `Stacks.Picard.FirstCohomology.torsorDifference_generator` — the difference of two generators
  is their transition unit.
* `Stacks.Picard.FirstCohomology.cochainPullback_transitionCocycle` — the transition cocycle of
  the pulled-back generators.
* `Stacks.Picard.FirstCohomology.edge_map_torsorClass_generatorTorsor` — Tag 09NU is natural in
  the scheme, read on generator torsors.
* `Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality` and
  `Stacks.Picard.FirstCohomology.h1UnitsAddEquivOfScheme_naturality` — the commuting square,
  over `Stacks.Picard.ofScheme`.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Picard.FirstCohomology

open Stacks.Cohomology.LerayLowDegree (abelianSections abelianPushforward abelianCohomology
  abelianSheafHasSheafify abelianEdgeMap abelianEdgeMap_eq)
open Stacks.Cohomology.CechOne (push push_apply push_cechD push_comp push_congr restr_app
  sheaf_hom_app_apply_congr sheaf_comp_app_apply_congr inter_le_of_eq_iSup
  CechOneResolutionRepresentative
  abelianResolutionSections cechH1ToRightDerivedSections cechH1ToRightDerivedSections_apply
  nonempty_cechOneResolutionRepresentative repValue repValue_def coboundary_eq restriction_eq
  resolutionIso)

attribute [local instance] abelianSheafHasSheafify

variable {X' X : TopCat.{u}} (f : X' ⟶ X) {I : Type u} (Ui : I → Opens X) (Vi : I → Opens X')

/-- Taking preimages of opens along a continuous map is monotone. -/
private theorem preimage_mono {V W : Opens X} (h : W ≤ V) :
    (Opens.map f).obj W ≤ (Opens.map f).obj V :=
  ((Opens.map f).map (homOfLE h)).le

/-- The preimage cover covers the whole space. -/
private theorem top_eq_iSup_preimage (hUi : (⊤ : Opens X) = ⨆ i, Ui i) :
    (⊤ : Opens X') = ⨆ i, (Opens.map f).obj (Ui i) := by
  refine Opens.ext ?_
  rw [Opens.coe_iSup]
  change Set.univ = ⋃ i, f ⁻¹' (Ui i : Set X)
  rw [← Set.preimage_iUnion, ← Opens.coe_iSup, ← hUi]
  rfl

/-- A cover of the source refining the preimage of a cover of the target refines it on every
finite intersection. -/
theorem inter_le_preimage_inter (hle : ∀ i, Vi i ≤ (Opens.map f).obj (Ui i)) {p : ℕ}
    (i : Fin p → I) :
    CechCochains.inter Vi i ≤ (Opens.map f).obj (CechCochains.inter Ui i) :=
  fun _ hx => CechCochains.mem_inter Ui
    (fun k => hle (i k) (CechCochains.inter_le Vi i k hx))

/-- A Čech cochain of a direct image, read as a Čech cochain on the source for a cover
refining the preimage cover. -/
def cochainPullback (hle : ∀ i, Vi i ≤ (Opens.map f).obj (Ui i))
    (A : TopCat.Sheaf AddCommGrpCat.{u} X') (p : ℕ) :
    CechCochains.Cochain Ui ((abelianPushforward.{u, u} f).obj A).obj p →+
      CechCochains.Cochain Vi A.presheaf p where
  toFun c := fun i =>
    CechCochains.restr A.presheaf (inter_le_preimage_inter f Ui Vi hle i) (c i)
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

/-- The value of a transported Čech cochain is the restriction of its value upstairs. -/
theorem cochainPullback_apply (hle : ∀ i, Vi i ≤ (Opens.map f).obj (Ui i))
    (A : TopCat.Sheaf AddCommGrpCat.{u} X') (p : ℕ)
    (c : CechCochains.Cochain Ui ((abelianPushforward.{u, u} f).obj A).obj p)
    (i : Fin (p + 1) → I) :
    cochainPullback f Ui Vi hle A p c i =
      CechCochains.restr A.presheaf (inter_le_preimage_inter f Ui Vi hle i) (c i) := rfl

/-- Reading a Čech cochain of a direct image on the refining cover commutes with the Čech
differential. -/
theorem cochainPullback_cechD (hle : ∀ i, Vi i ≤ (Opens.map f).obj (Ui i))
    (A : TopCat.Sheaf AddCommGrpCat.{u} X') (p : ℕ)
    (c : CechCochains.Cochain Ui ((abelianPushforward.{u, u} f).obj A).obj p) :
    CechCochains.cechD Vi A.presheaf p (cochainPullback f Ui Vi hle A p c) =
      cochainPullback f Ui Vi hle A (p + 1)
        (CechCochains.cechD Ui ((abelianPushforward.{u, u} f).obj A).obj p c) := by
  funext i
  change (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr A.presheaf (CechCochains.inter_le_omit Vi i j)
          (CechCochains.restr A.presheaf (inter_le_preimage_inter f Ui Vi hle (i ∘ j.succAbove))
            (c (i ∘ j.succAbove)))) =
      CechCochains.restr A.presheaf (inter_le_preimage_inter f Ui Vi hle i)
        (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr A.presheaf (preimage_mono f (CechCochains.inter_le_omit Ui i j))
            (c (i ∘ j.succAbove)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact (CechCochains.restr_restr A.presheaf _ _ (c (i ∘ j.succAbove))).trans
    (CechCochains.restr_restr A.presheaf _ _ (c (i ∘ j.succAbove))).symm

section Edge

open Stacks.Cohomology.RightDerivedEdge (resolutionComparison ι_f_zero_comp_resolutionComparison)

variable (G : TopCat.Sheaf AddCommGrpCat.{u} X')
  (hUi : (⊤ : Opens X) = ⨆ i, Ui i) (hVi : (⊤ : Opens X') = ⨆ i, Vi i)
  (hle : ∀ i, Vi i ≤ (Opens.map f).obj (Ui i))

/-- The chosen injective resolution of the direct image. -/
private abbrev resPushforward : InjectiveResolution ((abelianPushforward.{u, u} f).obj G) :=
  injectiveResolution ((abelianPushforward.{u, u} f).obj G)

/-- The chosen injective resolution on the source. -/
private abbrev resSource : InjectiveResolution G := injectiveResolution G

/-- The comparison of the two chosen resolutions over `f`. -/
private abbrev resComparison : (resPushforward f G).cocomplex ⟶
    ((abelianPushforward.{u, u} f).mapHomologicalComplex (.up ℕ)).obj (resSource G).cocomplex :=
  resolutionComparison (abelianPushforward.{u, u} f) G

/-- The injective-resolution representative of a Čech cocycle of a direct image, read on the
source along the comparison of the two chosen resolutions. -/
private def repPullback
    (z : CechCochains.cocycles1 Ui ((abelianPushforward.{u, u} f).obj G).obj)
    (z' : CechCochains.cocycles1 Vi G.presheaf)
    (hz : ∀ i : Fin 2 → I, z'.val i = cochainPullback f Ui Vi hle G 1 z.val i)
    (r : CechOneResolutionRepresentative X ⊤ Ui hUi
      ((abelianPushforward.{u, u} f).obj G) (resPushforward f G) z) :
    CechOneResolutionRepresentative X' ⊤ Vi hVi G (resSource G) z' where
  b := cochainPullback f Ui Vi hle ((resSource G).cocomplex.X 0) 0
    (push Ui ((resComparison f G).f 0).hom 0 r.b)
  cycle := HomologicalComplex.cyclesMap
    (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map (resComparison f G)) 1 r.cycle
  coboundary i := by
    have h2 : CechCochains.cechD Ui
          ((abelianPushforward.{u, u} f).obj ((resSource G).cocomplex.X 0)).obj 0
          (push Ui ((resComparison f G).f 0).hom 0 r.b) =
        push Ui (((abelianPushforward.{u, u} f).map ((resSource G).ι.f 0)).hom) 1 z.val := by
      refine Eq.trans (push_cechD Ui ((resComparison f G).f 0).hom 0 r.b).symm ?_
      refine Eq.trans (congrArg (fun c => push Ui ((resComparison f G).f 0).hom 1 c)
        (coboundary_eq X Ui ((abelianPushforward.{u, u} f).obj G) ⊤ hUi (resPushforward f G) r)) ?_
      refine ((push_comp Ui (((resPushforward f G).ι.f 0).hom)
        ((resComparison f G).f 0).hom 1 z.val).symm).trans ?_
      exact push_congr Ui _ (((abelianPushforward.{u, u} f).map ((resSource G).ι.f 0)).hom) 1 z.val
        (fun V x => sheaf_hom_app_apply_congr X
          (ι_f_zero_comp_resolutionComparison (abelianPushforward.{u, u} f) G) V x)
    refine Eq.trans (congrFun (cochainPullback_cechD f Ui Vi hle ((resSource G).cocomplex.X 0) 0
      (push Ui ((resComparison f G).f 0).hom 0 r.b)) i) ?_
    refine Eq.trans (congrFun (congrArg (fun c => cochainPullback f Ui Vi hle
      ((resSource G).cocomplex.X 0) 1 c) h2) i) ?_
    refine Eq.trans (restr_app (((resSource G).ι.f 0).hom) (inter_le_preimage_inter f Ui Vi hle i)
      (z.val i)) ?_
    exact congrArg (((resSource G).ι.f 0).hom.app (op (CechCochains.inter Vi i))) (hz i).symm
  restriction i := by
    have hmap : (abelianResolutionSections X' ⊤ (resSource G)).iCycles 1
          (HomologicalComplex.cyclesMap
            (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map (resComparison f G)) 1
            r.cycle) =
        ((resComparison f G).f 1).hom.app (op (⊤ : Opens X))
          ((abelianResolutionSections X ⊤ (resPushforward f G)).iCycles 1 r.cycle) :=
      (ConcreteCategory.comp_apply _ _ r.cycle).symm.trans
        ((ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
            (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map
              (resComparison f G)) 1)
          r.cycle).trans (ConcreteCategory.comp_apply _ _ r.cycle))
    change CechCochains.restr ((resSource G).cocomplex.X 1).presheaf (inter_le_of_eq_iSup hVi i)
          ((abelianResolutionSections X' ⊤ (resSource G)).iCycles 1
            (HomologicalComplex.cyclesMap
              (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map
                (resComparison f G)) 1
              r.cycle)) =
        -(((resSource G).cocomplex.d 0 1).hom.app (op (CechCochains.inter Vi i))
          (cochainPullback f Ui Vi hle ((resSource G).cocomplex.X 0) 0
            (push Ui ((resComparison f G).f 0).hom 0 r.b) i))
    rw [hmap]
    refine Eq.trans (CechCochains.restr_restr ((resSource G).cocomplex.X 1).presheaf
      (preimage_mono f (inter_le_of_eq_iSup hUi i)) (inter_le_preimage_inter f Ui Vi hle i)
      (((resComparison f G).f 1).hom.app (op (⊤ : Opens X))
        ((abelianResolutionSections X ⊤ (resPushforward f G)).iCycles 1 r.cycle))).symm ?_
    refine Eq.trans (congrArg (fun y => CechCochains.restr
      ((resSource G).cocomplex.X 1).presheaf (inter_le_preimage_inter f Ui Vi hle i) y)
      (restr_app (((resComparison f G).f 1).hom) (inter_le_of_eq_iSup hUi i)
        ((abelianResolutionSections X ⊤ (resPushforward f G)).iCycles 1 r.cycle))) ?_
    rw [restriction_eq X Ui ((abelianPushforward.{u, u} f).obj G) ⊤ hUi (resPushforward f G) r i,
      map_neg,
      sheaf_comp_app_apply_congr X ((resPushforward f G).cocomplex.d 0 1) ((resComparison f G).f 1)
        ((resComparison f G).f 0)
        ((((abelianPushforward.{u, u} f).mapHomologicalComplex (.up ℕ)).obj
          (resSource G).cocomplex).d 0 1)
        ((resComparison f G).comm 0 1).symm (CechCochains.inter Ui i) (r.b i)]
    refine Eq.trans (map_neg (CechCochains.restr ((resSource G).cocomplex.X 1).presheaf
      (inter_le_preimage_inter f Ui Vi hle i)) _) ?_
    refine congrArg (fun y : ToType (((resSource G).cocomplex.X 1).presheaf.obj
      (op (CechCochains.inter Vi i))) => -y) ?_
    exact restr_app (((resSource G).cocomplex.d 0 1).hom) (inter_le_preimage_inter f Ui Vi hle i)
      (((resComparison f G).f 0).hom.app (op (CechCochains.inter Ui i)) (r.b i))

/-- **The first Leray edge map on Čech classes.**  For a continuous map `f : X' ⟶ X`, an abelian
sheaf `G` on `X'`, a cover `Ui` of `X` and a cover `Vi` of `X'` refining its preimage, the edge
map `H¹(X, f_*G) ⟶ H¹(X', G)` sends the Čech class of a cocycle of `f_*G` on `Ui` to the Čech
class of the cocycle read on `Vi`. -/
theorem abelianEdgeMap_cechH1ToRightDerivedSections
    (z : CechCochains.cocycles1 Ui ((abelianPushforward.{u, u} f).obj G).obj)
    (z' : CechCochains.cocycles1 Vi G.presheaf)
    (hz : ∀ i : Fin 2 → I, z'.val i = cochainPullback f Ui Vi hle G 1 z.val i) :
    (abelianEdgeMap.{u, u} f 1).app G
        (cechH1ToRightDerivedSections X ⊤ Ui hUi ((abelianPushforward.{u, u} f).obj G)
          (CechCochains.cls Ui ((abelianPushforward.{u, u} f).obj G).obj z)) =
      cechH1ToRightDerivedSections X' ⊤ Vi hVi G (CechCochains.cls Vi G.presheaf z') := by
  obtain ⟨r⟩ := nonempty_cechOneResolutionRepresentative X Ui
    ((abelianPushforward.{u, u} f).obj G) ⊤ hUi (resPushforward f G) z
  refine Eq.trans (congrArg (fun y => (abelianEdgeMap.{u, u} f 1).app G y)
    (cechH1ToRightDerivedSections_apply X ⊤ Ui hUi ((abelianPushforward.{u, u} f).obj G)
      (resPushforward f G) z r)) ?_
  refine Eq.trans ?_ (cechH1ToRightDerivedSections_apply X' ⊤ Vi hVi G (resSource G) z'
    (repPullback f Ui Vi G hUi hVi hle z z' hz r)).symm
  refine Eq.trans (ConcreteCategory.congr_hom
    (abelianEdgeMap_eq.{u, u} f G 1 (resSource G) (resPushforward f G) (resComparison f G)
      (ι_f_zero_comp_resolutionComparison (abelianPushforward.{u, u} f) G)) _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine congrArg (ConcreteCategory.hom (resolutionIso X' ⊤ G (resSource G) 1).inv) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom (HomologicalComplex.homologyMap
    (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map (resComparison f G)) 1))
      (CategoryTheory.Iso.inv_hom_id_apply _ _)) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ r.cycle).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (((abelianSections.{u, u} X ⊤).mapHomologicalComplex (.up ℕ)).map (resComparison f G)) 1)
    r.cycle) ?_
  exact ConcreteCategory.comp_apply _ _ r.cycle

end Edge

section Generator

open Stacks.Cohomology.SheafTorsor (Torsor torsorDifference torsorDifference_eq
  transitionCochain torsorTransitionCocycle torsorTransitionCocycle_val IsTransitionCocycle)
open Stacks.Cohomology.Generators (unitsSheaf generatorTorsorOfInvertible GeneratorTorsor)
open Stacks.SheafOfModules (GeneratorSections generatorRatioUnit generatorRatioUnit_val
  generatorRatioUnit_restrict generatorRatio_spec generatorRestrict pullbackGenerator
  pullbackGenerator_restrict generatorRatioUnit_pullbackGenerator)
open Stacks.RingedSpace (structureIsSheaf structureRingSheaf)
open Stacks.RingedSpace (pullbackFunctor)

/-- The difference of two generators of an invertible module, as sections of its torsor of
generators, is their transition unit. -/
theorem torsorDifference_generator (R : RingedSpace.{u, u})
    [∀ x : R, IsLocalRing (R.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf R.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible R.sheaf.obj
      (structureSheaf R.sheaf).property L)
    (U : Opens R) (a b : (generatorTorsorOfInvertible R L hL).toTorsor.F.obj U) :
    torsorDifference (generatorTorsorOfInvertible R L hL).toTorsor a b =
      Additive.ofMul (generatorRatioUnit L U b a) := by
  refine torsorDifference_eq (generatorTorsorOfInvertible R L hL).toTorsor a b _ ?_
  refine Subtype.ext (Eq.trans ((generatorTorsorOfInvertible R L hL).sectionsEquiv_smul U
    (generatorRatioUnit L U b a) b) ?_)
  refine Eq.trans ?_ (generatorRatio_spec L U b a).symm
  exact congrArg (fun r : (structureSheaf R.sheaf).obj.obj (op U) => r • b.val)
    (generatorRatioUnit_val L U b a)

/-- Restriction of sections of the sheaf of units is `Units.map` of restriction of functions. -/
private theorem restr_unitsSheaf_ofMul (R : RingedSpace.{u, u}) {U V : Opens R} (h : V ≤ U)
    (w : (R.presheaf.obj (op U))ˣ) :
    CechCochains.restr (unitsSheaf R).presheaf h (Additive.ofMul w) =
      Additive.ofMul (Units.map (R.presheaf.map (homOfLE h).op).hom.toMonoidHom w) := rfl

/-- Restriction in the torsor of generators is restriction of the generating section. -/
private theorem torsorRes_eq_generatorRestrict (R : RingedSpace.{u, u})
    [∀ x : R, IsLocalRing (R.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf R.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible R.sheaf.obj
      (structureSheaf R.sheaf).property L)
    {U V : Opens R} (h : V ≤ U) (x : (generatorTorsorOfInvertible R L hL).toTorsor.F.obj U) :
    (generatorTorsorOfInvertible R L hL).toTorsor.F.res h x = generatorRestrict L h x :=
  Subtype.ext ((generatorTorsorOfInvertible R L hL).sectionsEquiv_restrict h x)

/-- Two successive restrictions of a generator compose. -/
private theorem generatorRestrict_generatorRestrict (R : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf R.sheaf))
    {U V W : Opens R} (h : V ≤ U) (k : W ≤ V) (x : GeneratorSections R L U) :
    generatorRestrict L k (generatorRestrict L h x) = generatorRestrict L (k.trans h) x :=
  Subtype.ext (by
    change L.val.map (homOfLE k).op (L.val.map (homOfLE h).op x.val) =
      L.val.map (homOfLE (k.trans h)).op x.val
    rw [← PresheafOfModules.map_comp_apply]
    congr 2)

section Pullback

open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)

variable {X' X : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property L)
  {I : Type u} (Ui : I → Opens X)
  (s : ∀ i, GeneratorSections X.toRingedSpace L (Ui i))

/-- The pullback of an invertible module along a morphism of schemes. -/
abbrev pullbackModule : X'.Modules := (pullbackFunctor f.toLRSHom.toShHom).obj L

/-- The pullback of an invertible module is invertible. -/
theorem pullbackModule_isInvertible (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property L) :
    Stacks.SheafOfModules.IsInvertible X'.presheaf
    (Stacks.RingedSpace.structureRingSheaf X'.toRingedSpace).property (pullbackModule f L) :=
  @Stacks.RingedSpace.isInvertible_modulePullback X'.toRingedSpace X.toRingedSpace
    f.toLRSHom.toShHom L hL

/-- The preimage of a cover of the target. -/
abbrev preimageCover : I → Opens X' := fun i => (Opens.map f.base).obj (Ui i)

/-- The preimage cover refines itself. -/
theorem preimageCover_le : ∀ i, preimageCover f Ui i ≤ (Opens.map f.base).obj (Ui i) :=
  fun _ => le_rfl

/-- The pullback along `f` of the `i`-th member of a family of local generators of `L`, a
generator of the pullback module on the preimage of the `i`-th open of the cover. -/
abbrev preimageGenerator (i : I) :
    GeneratorSections X'.toRingedSpace (pullbackModule f L) (preimageCover f Ui i) :=
  pullbackGenerator f L hL (Ui i) (s i)

/-- The generators of `L` on a cover, restricted to one of the finite intersections. -/
private abbrev interGenerator (i : Fin 2 → I) (k : Fin 2) :
    GeneratorSections X.toRingedSpace L (CechCochains.inter Ui i) :=
  generatorRestrict L (CechCochains.inter_le Ui i k) (s (i k))

/-- **The transition cocycle of the pulled-back generators is the transition cocycle of the
generators, pushed along `f` and read on the preimage cover.** -/
theorem cochainPullback_transitionCocycle (i : Fin 2 → I) :
    cochainPullback f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
        (unitsSheaf X'.toRingedSpace) 1
        (push Ui (unitsPushforwardMap f).hom 1
          (torsorTransitionCocycle
            (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s).val) i =
      torsorDifference
        (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
          (pullbackModule_isInvertible f L hL)).toTorsor
        ((generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
          (pullbackModule_isInvertible f L hL)).toTorsor.F.res
            (iInf_le (fun k => preimageCover f Ui (i k)) 1) (preimageGenerator f L hL Ui s (i 1)))
        ((generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
          (pullbackModule_isInvertible f L hL)).toTorsor.F.res
            (iInf_le (fun k => preimageCover f Ui (i k)) 0)
              (preimageGenerator f L hL Ui s (i 0))) := by
  have hdown := inter_le_preimage_inter f.base Ui (preimageCover f Ui) (preimageCover_le f Ui) i
  -- the downstairs generators, restricted to the preimage of the intersection
  have hres : ∀ k : Fin 2,
      (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
          (pullbackModule_isInvertible f L hL)).toTorsor.F.res
          (iInf_le (fun k => preimageCover f Ui (i k)) k) (preimageGenerator f L hL Ui s (i k)) =
        generatorRestrict (pullbackModule f L) hdown
          (pullbackGenerator f L hL (CechCochains.inter Ui i) (interGenerator L Ui s i k)) := by
    intro k
    refine Eq.trans (torsorRes_eq_generatorRestrict X'.toRingedSpace (pullbackModule f L)
      (pullbackModule_isInvertible f L hL) _ _) ?_
    refine Eq.trans (generatorRestrict_generatorRestrict X'.toRingedSpace (pullbackModule f L)
      (preimage_mono f.base (CechCochains.inter_le Ui i k)) hdown
        (preimageGenerator f L hL Ui s (i k))).symm ?_
    exact congrArg (generatorRestrict (pullbackModule f L) hdown)
      (pullbackGenerator_restrict f L hL (CechCochains.inter_le Ui i k) (s (i k)))
  have hzv : (torsorTransitionCocycle
        (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s).val i =
      Additive.ofMul (generatorRatioUnit L (CechCochains.inter Ui i)
        (interGenerator L Ui s i 0) (interGenerator L Ui s i 1)) := by
    refine Eq.trans (torsorTransitionCocycle_val
      (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s i) ?_
    refine Eq.trans (torsorDifference_generator X.toRingedSpace L hL
      (CechCochains.inter Ui i) _ _) ?_
    exact congrArg (fun w => Additive.ofMul w)
      (congrArg₂ (generatorRatioUnit L (CechCochains.inter Ui i))
        (torsorRes_eq_generatorRestrict X.toRingedSpace L hL _ (s (i 0)))
        (torsorRes_eq_generatorRestrict X.toRingedSpace L hL _ (s (i 1))))
  rw [hres 0, hres 1]
  refine Eq.trans ?_ (torsorDifference_generator X'.toRingedSpace (pullbackModule f L)
    (pullbackModule_isInvertible f L hL) (CechCochains.inter (preimageCover f Ui) i) _ _).symm
  have hRHS : generatorRatioUnit (pullbackModule f L) (CechCochains.inter (preimageCover f Ui) i)
        (generatorRestrict (pullbackModule f L) hdown
          (pullbackGenerator f L hL (CechCochains.inter Ui i) (interGenerator L Ui s i 0)))
        (generatorRestrict (pullbackModule f L) hdown
          (pullbackGenerator f L hL (CechCochains.inter Ui i) (interGenerator L Ui s i 1))) =
      Units.map (X'.presheaf.map (homOfLE hdown).op).hom.toMonoidHom
        (Units.map (f.app (CechCochains.inter Ui i)).hom.toMonoidHom
          (generatorRatioUnit L (CechCochains.inter Ui i)
            (interGenerator L Ui s i 0) (interGenerator L Ui s i 1))) := by
    refine Eq.trans (generatorRatioUnit_restrict (pullbackModule f L) hdown
      (pullbackGenerator f L hL (CechCochains.inter Ui i) (interGenerator L Ui s i 0))
      (pullbackGenerator f L hL (CechCochains.inter Ui i) (interGenerator L Ui s i 1))) ?_
    exact congrArg
      (fun w => Units.map (X'.presheaf.map (homOfLE hdown).op).hom.toMonoidHom w)
      (generatorRatioUnit_pullbackGenerator f L hL (CechCochains.inter Ui i)
        (interGenerator L Ui s i 0) (interGenerator L Ui s i 1))
  refine Eq.trans ?_ (congrArg (fun w => Additive.ofMul w) hRHS).symm
  refine (cochainPullback_apply f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
    (unitsSheaf X'.toRingedSpace) 1 _ i).trans ?_
  rw [push_apply, hzv]
  refine Eq.trans (congrArg
    (fun y => CechCochains.restr (unitsSheaf X'.toRingedSpace).presheaf hdown y)
    (unitsPushforwardMap_app f (CechCochains.inter Ui i)
      (generatorRatioUnit L (CechCochains.inter Ui i)
        (interGenerator L Ui s i 0) (interGenerator L Ui s i 1)))) ?_
  exact restr_unitsSheaf_ofMul X'.toRingedSpace hdown _

/-- **The pulled-back generators have the pushed-forward transition cocycle.** -/
theorem isTransitionCocycle_pullbackGenerator
    (z' : CechCochains.cocycles1 (preimageCover f Ui) (unitsSheaf X'.toRingedSpace).presheaf)
    (hz' : ∀ i : Fin 2 → I, z'.val i =
      cochainPullback f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
        (unitsSheaf X'.toRingedSpace) 1
        (push Ui (unitsPushforwardMap f).hom 1
          (torsorTransitionCocycle
            (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s).val) i) :
    IsTransitionCocycle
      (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
        (pullbackModule_isInvertible f L hL)).toTorsor (preimageCover f Ui)
        (preimageGenerator f L hL Ui s) z' := by
  intro i
  refine Eq.trans (congrArg (fun d =>
      (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
        (pullbackModule_isInvertible f L hL)).toTorsor.action.act (Multiplicative.ofAdd d)
      ((generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
        (pullbackModule_isInvertible f L hL)).toTorsor.F.res
          (iInf_le (fun k => preimageCover f Ui (i k)) 0) (preimageGenerator f L hL Ui s (i 0))))
    ((hz' i).trans (cochainPullback_transitionCocycle f L hL Ui s i))) ?_
  exact Stacks.Cohomology.SheafTorsor.torsorDifference_act _ _ _

end Pullback

section Naturality

open Stacks.Cohomology.SheafTorsor (torsorClassEquivSheafCohomologyOne
  torsorClassEquivSheafCohomologyOne_of_cocycle torsorTransitionCocycle_spec)
open Stacks.Cohomology.CechOne (cechH1ToRightDerivedSections_naturality cechD_push)
open Stacks.GlueSquishUnits (unitsPushforwardMap)

variable {X' X : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property L)

/-- **Stacks Tag 09NU is natural in the scheme, read on generator torsors.**  For a morphism of
schemes `f : X' ⟶ X` and an invertible `𝒪_X`-module `L`, the first-cohomology class of the
torsor of generators of `L`, carried along `𝒪_X^* ⟶ f_*𝒪_{X'}^*` and then along the first Leray
edge map, is the class of the torsor of generators of `f^*L`. -/
theorem edge_map_torsorClass_generatorTorsor :
    (abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f)
          (torsorClassEquivSheafCohomologyOne _ (unitsSheaf X.toRingedSpace)
            (Quotient.mk _ (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor))) =
      torsorClassEquivSheafCohomologyOne _ (unitsSheaf X'.toRingedSpace)
        (Quotient.mk _ (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
          (pullbackModule_isInvertible f L hL)).toTorsor) := by
  classical
  have hrank := Stacks.Cohomology.Generators.isFiniteLocallyFreeOfRank_one_of_isInvertible
    X.toRingedSpace L hL
  choose Ui hmem hne using fun x : (X : Type u) =>
    @Stacks.Cohomology.Generators.exists_generator_section X.toRingedSpace L hrank x
  have hUi : (⊤ : Opens X) = ⨆ x, Ui x :=
    le_antisymm (fun x _ => Opens.mem_iSup.2 ⟨x, hmem x⟩) le_top
  let s : ∀ x : (X : Type u), GeneratorSections X.toRingedSpace L (Ui x) := fun x => (hne x).some
  let z : CechCochains.cocycles1 Ui (unitsSheaf X.toRingedSpace).presheaf :=
    torsorTransitionCocycle (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s
  let z₂ : CechCochains.cocycles1 Ui
      ((abelianPushforward.{u, u} f.base).obj (unitsSheaf X'.toRingedSpace)).obj :=
    ⟨push Ui (unitsPushforwardMap f).hom 1 z.val,
      cechD_push Ui (unitsPushforwardMap f).hom 1 z.val z.2⟩
  let z₃ : CechCochains.cocycles1 (preimageCover f Ui) (unitsSheaf X'.toRingedSpace).presheaf :=
    ⟨cochainPullback f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
        (unitsSheaf X'.toRingedSpace) 1 z₂.val,
      (cochainPullback_cechD f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
          (unitsSheaf X'.toRingedSpace) 1 z₂.val).trans
        ((congrArg (fun c => cochainPullback f.base Ui (preimageCover f Ui) (preimageCover_le f Ui)
          (unitsSheaf X'.toRingedSpace) 2 c) z₂.2).trans (map_zero _))⟩
  refine Eq.trans (congrArg (fun y => (abelianEdgeMap.{u, u} f.base 1).app
      (unitsSheaf X'.toRingedSpace)
      ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) y))
    (torsorClassEquivSheafCohomologyOne_of_cocycle _ (unitsSheaf X.toRingedSpace)
      (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui hUi s z
      (torsorTransitionCocycle_spec
        (generatorTorsorOfInvertible X.toRingedSpace L hL).toTorsor Ui s))) ?_
  refine Eq.trans (congrArg (fun y => (abelianEdgeMap.{u, u} f.base 1).app
      (unitsSheaf X'.toRingedSpace) y)
    (cechH1ToRightDerivedSections_naturality _ ⊤ Ui hUi (unitsPushforwardMap f) z z₂
      (fun _ => rfl))) ?_
  refine Eq.trans (abelianEdgeMap_cechH1ToRightDerivedSections f.base Ui (preimageCover f Ui)
    (unitsSheaf X'.toRingedSpace) hUi (top_eq_iSup_preimage f.base Ui hUi) (preimageCover_le f Ui)
    z₂ z₃ (fun _ => rfl)) ?_
  exact (torsorClassEquivSheafCohomologyOne_of_cocycle _ (unitsSheaf X'.toRingedSpace)
    (generatorTorsorOfInvertible X'.toRingedSpace (pullbackModule f L)
      (pullbackModule_isInvertible f L hL)).toTorsor (preimageCover f Ui)
    (top_eq_iSup_preimage f.base Ui hUi) (preimageGenerator f L hL Ui s) z₃
    (isTransitionCocycle_pullbackGenerator f L hL Ui s z₃ (fun _ => rfl))).symm

section Assembly

open Stacks.GluePicard (h1UnitsAddEquivSmallPicard picardModelAddEquiv picardModelAddEquiv_classOf
  exists_classOf)
open Stacks.Cohomology.Generators (h1UnitsAddEquivPicardGroup
  h1UnitsAddEquivPicardGroup_symm_classOf)

/-- First cohomology of the sheaf of units of a scheme, in the derived-functor spelling. -/
abbrev h1UnitsRightDerived (Y : Scheme.{u}) : AddCommGrpCat.{u} :=
  (abelianCohomology.{u, u} _ ⊤ 1).obj (unitsSheaf Y.toRingedSpace)

/-- **Stacks Tag 09NU over `Stacks.Picard.ofScheme`**: first cohomology of the sheaf of units of
a scheme is its Picard group. -/
@[ega "0 5.4.7" "special case", ega "IV 21.3.6" "special case", sga "1 XI 6.4"]
def h1UnitsAddEquivPicard (Y : Scheme.{u}) : h1UnitsRightDerived Y ≃+ Stacks.Picard.ofScheme Y :=
  (h1UnitsAddEquivSmallPicard Y).trans (picardModelAddEquiv Y.toRingedSpace).symm

/-- The identification of Tag 09NU carries the class of the generator torsor of an invertible
module to the Picard class of that module. -/
theorem h1UnitsAddEquivPicard_symm_classOf (Y : Scheme.{u}) (M : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).property M) :
    (h1UnitsAddEquivPicard Y).symm (Stacks.SheafOfModules.picardClass Y.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M hM) =
      Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne _
        (unitsSheaf Y.toRingedSpace)
        (Quotient.mk _ (generatorTorsorOfInvertible Y.toRingedSpace M hM).toTorsor) := by
  refine Eq.trans (congrArg (fun y => (h1UnitsAddEquivSmallPicard Y).symm y)
    (picardModelAddEquiv_classOf Y.toRingedSpace M hM)) ?_
  exact h1UnitsAddEquivPicardGroup_symm_classOf Y.toRingedSpace M hM

/-- **Naturality of Stacks Tag 09NU in a morphism of schemes.**  For `f : X' ⟶ X`
the square formed by the identifications of Tag 09NU, by pullback of Picard classes, and by the
map on first cohomology induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*` followed by the first Leray edge map,
commutes. -/
theorem h1UnitsAddEquivPicard_naturality {X' X : Scheme.{u}} (f : X' ⟶ X)
    (c : h1UnitsRightDerived X) :
    h1UnitsAddEquivPicard X'
        ((abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace)
          ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) c)) =
      Stacks.Picard.schemePullbackClassHom f (h1UnitsAddEquivPicard X c) := by
  obtain ⟨L, hL, hLc⟩ := exists_classOf X.toRingedSpace (h1UnitsAddEquivPicard X c)
  have hc : c = (h1UnitsAddEquivPicard X).symm
      (Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL) := by
    rw [hLc, AddEquiv.symm_apply_apply]
  have h1 : (abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) c) =
      (h1UnitsAddEquivPicard X').symm (Stacks.SheafOfModules.picardClass X'.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) (pullbackModule f L)
        (pullbackModule_isInvertible f L hL)) := by
    refine Eq.trans (congrArg (fun y => (abelianEdgeMap.{u, u} f.base 1).app
        (unitsSheaf X'.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) y))
      (hc.trans (h1UnitsAddEquivPicard_symm_classOf X L hL))) ?_
    refine Eq.trans (edge_map_torsorClass_generatorTorsor f L hL) ?_
    exact (h1UnitsAddEquivPicard_symm_classOf X' (pullbackModule f L)
      (pullbackModule_isInvertible f L hL)).symm
  rw [h1, AddEquiv.apply_symm_apply, ← hLc]
  exact (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom L hL).symm

/-- **Pullback on native first cohomology of the sheaf of units.**  Native cohomology is read
through the chosen identification `Stacks.GluePicard.h1Iso` with the first right-derived functor
of sections, where the map is `𝒪_X^* ⟶ f_*𝒪_{X'}^*` followed by the first Leray edge map. -/
def h1NativeUnitsPullback {X' X : Scheme.{u}} (f : X' ⟶ X) :
    (Stacks.Cohomology.AbelianColimit.H'functor (X := (X : Type u)) ⊤ 1).obj
        (unitsSheaf X.toRingedSpace) ⟶
      (Stacks.Cohomology.AbelianColimit.H'functor (X := (X' : Type u)) ⊤ 1).obj
        (unitsSheaf X'.toRingedSpace) :=
  ((Stacks.GluePicard.h1Iso (X : Type u)).app (unitsSheaf X.toRingedSpace)).hom ≫
    (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) ≫
    (abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace) ≫
    ((Stacks.GluePicard.h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)).inv

/-- **Naturality of Stacks Tag 09NU in a morphism of schemes, in the spelling of
`Stacks.GluePicard.h1UnitsAddEquivOfScheme`.**  The square formed by the identifications of
Tag 09NU, by pullback of Picard classes, and by pullback on native first cohomology of the
sheaf of units commutes. -/
theorem h1UnitsAddEquivOfScheme_naturality {X' X : Scheme.{u}} (f : X' ⟶ X)
    (c : (Stacks.Cohomology.AbelianColimit.H'functor (X := (X : Type u)) ⊤ 1).obj
      (unitsSheaf X.toRingedSpace)) :
    Stacks.GluePicard.h1UnitsAddEquivOfScheme X' (h1NativeUnitsPullback f c) =
      Stacks.Picard.schemePullbackClassHom f
        (Stacks.GluePicard.h1UnitsAddEquivOfScheme X c) := by
  refine Eq.trans ?_ (h1UnitsAddEquivPicard_naturality f
    (((Stacks.GluePicard.h1Iso (X : Type u)).app (unitsSheaf X.toRingedSpace)).hom c))
  refine congrArg (fun y => h1UnitsAddEquivPicard X' y) ?_
  change ConcreteCategory.hom
      (((Stacks.GluePicard.h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)).inv ≫
        ((Stacks.GluePicard.h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)).hom) _ = _
  rw [CategoryTheory.Iso.inv_hom_id]
  rfl

end Assembly

end Naturality

end Generator

end Stacks.Picard.FirstCohomology

end

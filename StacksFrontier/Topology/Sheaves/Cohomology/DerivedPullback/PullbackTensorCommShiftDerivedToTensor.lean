module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftComparisons
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShiftResolution
public import StacksFrontier.Homology.KFlat.BifunctorComplexModelsShift
import StacksCore.Tactic.StacksAttribute

/-!
# The shift compatibility of Tag 079U reduced to K-flat cochain complexes

`Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShift₂` is the compatibility with the
shifts in each variable of the curried canonical map `QK ⊗^L_{𝒪_Z} QL ⟶ Q(Tot(K ⊗_{𝒪_Z} L))` of
[Stacks, Tag 06YU], for all pairs of cochain complexes. This file shows that it follows from the
same compatibility over K-flat cochain complexes: every complex receives a quasi-isomorphism from
a K-flat one ([Stacks, Tag 06YS]), and the source bifunctor `(K, L) ↦ QK ⊗^L QL` inverts
quasi-isomorphisms in each variable.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShiftOnKFlat`: the shift
  compatibility over K-flat cochain complexes, one condition per variable.
* `Stacks.Cohomology.DerivedPullbackTensor.commShift_app_of_kFlatResolution` and
  `Stacks.Cohomology.DerivedPullbackTensor.commShift_flipApp_of_kFlatResolution`: the shift
  compatibility in each variable at an arbitrary complex of the other.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShift₂_of_kFlat`:
  `DerivedToTensorCommShiftOnKFlat Z` implies `DerivedToTensorCommShift₂ Z`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-! ### A functor isomorphic to one inverting a morphism inverts it too -/

/-- **A functor isomorphic to one which inverts a morphism inverts it too.** -/
theorem isIso_map_of_natIso {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} (e : F ≅ F')
    {X Y : C} (p : X ⟶ Y) (h : IsIso (F.map p)) : IsIso (F'.map p) := by
  have hc : F'.map p = (e.app X).inv ≫ F.map p ≫ (e.app Y).hom := by
    rw [Iso.app_inv, Iso.app_hom, e.hom.naturality p, ← Category.assoc, e.inv_hom_id_app,
      Category.id_comp]
  rw [hc]
  infer_instance

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The K-flat cochain complexes of `𝒪_Z`-modules -/

/-- The K-flat cochain complexes of `𝒪_Z`-modules, as an object property of the cochain
complexes. -/
abbrev kFlatComplexesOn : ObjectProperty (CochainComplex (Modules Z) ℤ) :=
  CochainComplex.KFlatBifunctor.kFlatComplexes
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)

/-- **Every cochain complex of `𝒪_Z`-modules receives a quasi-isomorphism from a K-flat one**:
there is a morphism to it from an object of `kFlatComplexesOn Z` which `DerivedCategory.Q`
inverts. -/
theorem exists_kFlatComplex_resolution (G : CochainComplex (Modules Z) ℤ) :
    ∃ (P : (kFlatComplexesOn Z).FullSubcategory) (p : (kFlatComplexesOn Z).ι.obj P ⟶ G),
      IsIso (DerivedCategory.Q.map p) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Z.sheaf G
  refine ⟨⟨P, hP⟩, p, ?_⟩
  rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]

/-! ### The source bifunctor inverts the resolutions -/

/-- **The source of `derivedToTensorNatTrans`, curried, inverts every morphism of the first
variable which `DerivedCategory.Q` inverts.** -/
theorem isIso_curryComplexesDerivedTensor_map
    {K K' : CochainComplex (Modules Z) ℤ} (p : K ⟶ K') (hp : IsIso (DerivedCategory.Q.map p)) :
    IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).map p) := by
  refine isIso_map_of_natIso (curryComplexesDerivedTensorIso Z) p ?_
  exact inferInstanceAs (IsIso
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf ⋙
      (Functor.whiskeringLeft _ (DerivedCategory (Modules Z))
        (DerivedCategory (Modules Z))).obj DerivedCategory.Q).map (DerivedCategory.Q.map p)))

/-- **The source of `derivedToTensorNatTrans`, curried, inverts every morphism of the second
variable which `DerivedCategory.Q` inverts.** -/
theorem isIso_curryComplexesDerivedTensor_flip_map
    {L L' : CochainComplex (Modules Z) ℤ} (p : L ⟶ L') (hp : IsIso (DerivedCategory.Q.map p)) :
    IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).flip.map p) := by
  refine isIso_map_of_natIso
    ((flipFunctor _ _ _).mapIso (curryComplexesDerivedTensorIso Z)) p ?_
  have : ∀ K : CochainComplex (Modules Z) ℤ,
      IsIso ((((flipFunctor (CochainComplex (Modules Z) ℤ) (CochainComplex (Modules Z) ℤ)
        (DerivedCategory (Modules Z))).obj
          (curriedComplexesDerivedTensor Z)).map p).app K) := fun K =>
    inferInstanceAs (IsIso
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
        (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map p)))
  exact NatIso.isIso_of_isIso_app _

/-! ### The reduction -/

/-- **The shift compatibility of `derivedToTensorNatTrans` over K-flat cochain complexes.** Each
condition is a one-variable `CategoryTheory.NatTrans.CommShift` for the restriction of
`derivedToTensorNatTrans`, curried, along the inclusion of the K-flat complexes: the first in the
second variable at a fixed K-flat complex in the first, the second in the first variable at a
fixed K-flat complex in the second. -/
def DerivedToTensorCommShiftOnKFlat : Prop :=
  letI := curryComplexesDerivedTensor_commShift₂Int Z
  letI := curryComplexesTotal_commShift₂Int Z
  (∀ P : (kFlatComplexesOn Z).FullSubcategory,
      NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).app
          ((kFlatComplexesOn Z).ι.obj P))) ℤ) ∧
    ∀ P : (kFlatComplexesOn Z).FullSubcategory,
      NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexesOn Z).ι
        ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp
          ((kFlatComplexesOn Z).ι.obj P))) ℤ

/-- A functor inverting the morphisms inverted by `DerivedCategory.Q` inverts, for each complex,
a K-flat resolution and its shift by `a`. -/
private theorem exists_resolution_isIso_map_of_inverts {D : Type*} [Category D]
    (F : CochainComplex (Modules Z) ℤ ⥤ D)
    (hF : ∀ {K K' : CochainComplex (Modules Z) ℤ} (p : K ⟶ K'),
      IsIso (DerivedCategory.Q.map p) → IsIso (F.map p))
    (a : ℤ) (X : CochainComplex (Modules Z) ℤ) :
    ∃ (P : (kFlatComplexesOn Z).FullSubcategory) (p : (kFlatComplexesOn Z).ι.obj P ⟶ X),
      IsIso (F.map p) ∧ IsIso (F.map ((shiftFunctor (CochainComplex (Modules Z) ℤ) a).map p)) := by
  obtain ⟨P, p, hp⟩ := exists_kFlatComplex_resolution Z X
  exact ⟨P, p, hF p hp, hF _ (NatTrans.isIso_map_shiftFunctor_map (F := DerivedCategory.Q) p a)⟩

/-- Every cochain complex `X₁` receives a morphism `p` from a K-flat complex such that the
source bifunctor of `derivedToTensorNatTrans Z`, curried, inverts `p` and its shift by `a` in the
first variable. -/
theorem exists_resolution_isIso_map (a : ℤ) (X₁ : CochainComplex (Modules Z) ℤ) :
    ∃ (P : (kFlatComplexesOn Z).FullSubcategory) (p : (kFlatComplexesOn Z).ι.obj P ⟶ X₁),
      IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).map p) ∧
        IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).map
            ((shiftFunctor (CochainComplex (Modules Z) ℤ) a).map p)) := by
  exact exists_resolution_isIso_map_of_inverts Z _
    (isIso_curryComplexesDerivedTensor_map Z) a X₁

/-- Every cochain complex `X₂` receives a morphism `p` from a K-flat complex such that the
source bifunctor of `derivedToTensorNatTrans Z`, curried, inverts `p` and its shift by `a` in the
second variable. -/
theorem exists_resolution_isIso_flip_map (a : ℤ) (X₂ : CochainComplex (Modules Z) ℤ) :
    ∃ (P : (kFlatComplexesOn Z).FullSubcategory) (p : (kFlatComplexesOn Z).ι.obj P ⟶ X₂),
      IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).flip.map p) ∧
        IsIso ((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).flip.map
            ((shiftFunctor (CochainComplex (Modules Z) ℤ) a).map p)) := by
  exact exists_resolution_isIso_map_of_inverts Z _
    (isIso_curryComplexesDerivedTensor_flip_map Z) a X₂

/-- Under `DerivedToTensorCommShiftOnKFlat Z`, the component of `derivedToTensorNatTrans Z`,
curried in the second variable, at an arbitrary complex `X₁` of the first variable commutes with
the shift. -/
theorem commShift_app_of_kFlatResolution (h : DerivedToTensorCommShiftOnKFlat Z)
    (X₁ : CochainComplex (Modules Z) ℤ) :
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    letI := curryComplexesTotal_commShift₂Int Z
    NatTrans.CommShift ((Functor.curry.map (derivedToTensorNatTrans Z)).app X₁) ℤ := by
  let := curryComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesTotal_commShift₂Int Z
  obtain ⟨P₁, p₁, hp₁, -⟩ := exists_resolution_isIso_map Z 0 X₁
  refine NatTrans.CommShift₂.commShift_app_of_isIso_map _ _ p₁ ?_
  refine NatTrans.commShift_of_whiskerLeft_of_resolution (kFlatComplexesOn Z).ι _
    (fun a X₂ => ?_) (h.1 P₁)
  obtain ⟨P₂, p₂, -, hp₂⟩ := exists_resolution_isIso_flip_map Z a X₂
  exact ⟨P₂, p₂, inferInstanceAs (IsIso
    (((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).flip.map
        ((shiftFunctor (CochainComplex (Modules Z) ℤ) a).map p₂)).app
          ((kFlatComplexesOn Z).ι.obj P₁)))⟩

/-- Under `DerivedToTensorCommShiftOnKFlat Z`, the component of `derivedToTensorNatTrans Z`,
curried in the first variable, at an arbitrary complex `X₂` of the second variable commutes with
the shift. -/
theorem commShift_flipApp_of_kFlatResolution (h : DerivedToTensorCommShiftOnKFlat Z)
    (X₂ : CochainComplex (Modules Z) ℤ) :
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    letI := curryComplexesTotal_commShift₂Int Z
    NatTrans.CommShift ((Functor.curry.map (derivedToTensorNatTrans Z)).flipApp X₂) ℤ := by
  let := curryComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesTotal_commShift₂Int Z
  obtain ⟨P₂, p₂, hp₂, -⟩ := exists_resolution_isIso_flip_map Z 0 X₂
  refine NatTrans.CommShift₂.commShift_flipApp_of_isIso_map _ _ p₂ ?_
  refine NatTrans.commShift_of_whiskerLeft_of_resolution (kFlatComplexesOn Z).ι _
    (fun a X₁ => ?_) (h.2 P₂)
  obtain ⟨P₁, p₁, -, hp₁⟩ := exists_resolution_isIso_map Z a X₁
  exact ⟨P₁, p₁, inferInstanceAs (IsIso
    (((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).map
        ((shiftFunctor (CochainComplex (Modules Z) ℤ) a).map p₁)).app
          ((kFlatComplexesOn Z).ι.obj P₂)))⟩

/-- **Reduction to K-flat complexes.** The shift compatibility `DerivedToTensorCommShift₂ Z`
follows from the same compatibility `DerivedToTensorCommShiftOnKFlat Z` over K-flat cochain
complexes. -/
theorem derivedToTensorCommShift₂_of_kFlat (h : DerivedToTensorCommShiftOnKFlat Z) :
    DerivedToTensorCommShift₂ Z :=
  let := curryComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesTotal_commShift₂Int Z
  { commShift_app := commShift_app_of_kFlatResolution Z h
    commShift_flipApp := commShift_flipApp_of_kFlatResolution Z h }

end Stacks.Cohomology.DerivedPullbackTensor

end

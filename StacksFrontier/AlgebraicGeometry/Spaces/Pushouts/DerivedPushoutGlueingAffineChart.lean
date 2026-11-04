module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutChartCube
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalUnboundedDerivedIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal

/-!
# The isomorphism step of Stacks 0DL7 reduces to affine étale charts

Let `Y' = Y ⨿_X X'` be the pushout of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y` of algebraic spaces over a scheme `S`, with `j : Y ⟶ Y'` and `f' : X' ⟶ Y'`. The proof
of Stacks 0DL7 checks its isomorphism step (`AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso`)
étale locally on `Y'` and then on rings. This file carries out the étale-local part: the
isomorphism step follows from its case on an affine étale chart `W` of `Y'`, stated as the
proposition `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIsoOnAffineChart`, given that `f'` is
affine (`X' ×_{Y'} W` is then affine).

## Main definitions

* `AlgebraicGeometry.Space.PushoutGlueingIsIsoStep`: the isomorphism step for one square, one
  choice of models and one triple `(M, K', α)`.
* `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIsoOnAffineChart`: **the affine case** — the
  isomorphism step for the base change of the pushout square along an affine étale chart
  `W ⟶ Y'` over which `f'` is affine, at any models, for pseudo-coherent `M`, `K'`.

## Main results

* `isIso_of_forall_isIso_smallEtaleDerivedModulePullbackOfModels_pullbackFst` (namespace
  `AlgebraicGeometry.Space`): a morphism of `D(𝒪_T)` is invertible as soon as its restrictions
  to `T ×_{Y'} W` are, for the affine étale charts `W` of `Y'`, at any models (through the
  cohomology sheaves, from
  `AlgebraicGeometry.Space.isIso_of_forall_isIso_modulePullback_pullbackFst`).
* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels`: Stacks 08H4
  at any models.
* `AlgebraicGeometry.Space.pushoutGlueingMap_isIso_restrict` and
  `AlgebraicGeometry.Space.isIso_restrict_of_pushoutGlueingIsIsoStep`: the isomorphism step is
  étale local, for algebraic spaces at any models
  (`MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange_iso` at the cube of derived pullbacks,
  with the cube condition `AlgebraicGeometry.Space.smallEtaleDerivedPullback_cube` and the
  canonical form of Stacks 08GE).
* `AlgebraicGeometry.Space.derivedPushoutGlueingIsIso_of_onAffineChart`: **the isomorphism step of
  Stacks 0DL7 from its affine case** and the affineness of `f'`;
  `AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_onAffineChart`: Stacks 0DL7 from the
  same two inputs.

## What remains

The affine case `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIsoOnAffineChart` is the passage to
rings described in
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/DerivedPushoutEssentialImage.lean`, part 3. The
affineness of `f'` is given by the proof of Stacks 07VX, not by its statement,
or by Stacks 07VT.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/DerivedPushoutGlueingCubeSpaces.lean`, the
statement about the cube of derived pullbacks is `type_of%` an instantiated generic lemma, and
the shifts and triangulated structures of `Lf^*` read at other models
(`AlgebraicGeometry.Space.commShift_smallEtaleDerivedModulePullbackOfModels`,
`AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedModulePullbackOfModels`) are
instantiations of `Stacks.CategoryTheory.BaseChange.conjCommShift` and
`Stacks.CategoryTheory.BaseChange.conjCommShift_isTriangulated`, whose category structures are
unified from the functors. The restricted triple is asked for every isomorphism
`αW : LfW^* M_W ≅ LiW^* K'_W` rather than for the restriction of `α`: the restriction of `α`,
built from `Stacks.CategoryTheory.BaseChange.conjSquareIso`, has objects of the shape
`(F ⋙ G).obj M`, and comparing those with `G.obj (F.obj M)` at the derived categories of
algebraic spaces makes the kernel compare `F ⋙ G` with `G`, which it does not refute within its
budget. `MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange_iso` does that comparison over
abstract categories.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.CategoryTheory.BaseChange

section Conjugate

universe v₁ v₂ v₃ v₄

variable {C C' D D' : Type*} {_ : Category.{v₁} C} {_ : Category.{v₂} C'} {_ : Category.{v₃} D}
  {_ : Category.{v₄} D'} {_ : HasShift C ℤ} {_ : HasShift C' ℤ} {_ : HasShift D ℤ}
  {_ : HasShift D' ℤ} (eC : C ≌ C') (eD : D ≌ D') (F : C ⥤ D)

/-- A functor commuting with the shifts, read at other models through equivalences commuting with
the shifts, commutes with the shifts. -/
abbrev conjCommShift (hF : F.CommShift ℤ) (hC : eC.functor.CommShift ℤ)
    (hD : eD.functor.CommShift ℤ) : (eC.inverse ⋙ F ⋙ eD.functor).CommShift ℤ :=
  letI := eC.commShiftInverse ℤ
  inferInstance

/-- A triangulated functor read at other models through triangulated equivalences is
triangulated. The structure of the four categories is unified from the three functors. -/
theorem conjCommShift_isTriangulated {_ : Preadditive C} {_ : Preadditive C'}
    {_ : Preadditive D} {_ : Preadditive D'} {_ : HasZeroObject C} {_ : HasZeroObject C'}
    {_ : HasZeroObject D} {_ : HasZeroObject D'} {_ : ∀ n : ℤ, (shiftFunctor C n).Additive}
    {_ : ∀ n : ℤ, (shiftFunctor C' n).Additive} {_ : ∀ n : ℤ, (shiftFunctor D n).Additive}
    {_ : ∀ n : ℤ, (shiftFunctor D' n).Additive} {_ : Pretriangulated C} {_ : Pretriangulated C'}
    {_ : Pretriangulated D} {_ : Pretriangulated D'} {hF : F.CommShift ℤ}
    {hC : eC.functor.CommShift ℤ} {hD : eD.functor.CommShift ℤ} (tF : F.IsTriangulated)
    (tC : eC.functor.IsTriangulated) (tD : eD.functor.IsTriangulated) :
    letI := conjCommShift eC eD F hF hC hD
    (eC.inverse ⋙ F ⋙ eD.functor).IsTriangulated := by
  let := eC.commShiftInverse ℤ
  have := eC.commShift_of_functor ℤ
  have := Equivalence.IsTriangulated.mk' eC tC
  infer_instance

end Conjugate

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.Space

universe w w' w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄ u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Detection

attribute [local instance 5000] SheafOfModules.instAbelian

variable {T Y' : AlgebraicSpaces B S hS} (p : T ⟶ Y')

/-- **Isomorphisms in `D(𝒪_T)` are étale local on `Y'`, at arbitrary models.** For a morphism
`p : T ⟶ Y'` of algebraic spaces, a morphism of `D(𝒪_T)` whose derived pullback to `T ×_{Y'} W` is
invertible for every étale chart `W` of `Y'` with affine underlying scheme is invertible. -/
theorem isIso_of_forall_isIso_smallEtaleDerivedModulePullbackOfModels_pullbackFst
    (mT : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS T)))
    (mTW : ∀ W : SmallEtale B S hS Y'.obj, HasDerivedCategory.{w'} (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (pullback p (chartToSpace B S hS Y' W)))))
    {K L : @DerivedCategory _ _ _ mT} (φ : K ⟶ L)
    (h : ∀ W : SmallEtale B S hS Y'.obj, IsAffineChart B S hS Y'.obj W →
      IsIso ((smallEtaleDerivedModulePullbackOfModels B S hS
        (pullback.fst p (chartToSpace B S hS Y' W)) (mTW W) mT).map φ)) :
    IsIso φ := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS T))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS T.1 T.2)
  let e := StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS T))) mT
  suffices hφ : IsIso (e.inverse.map φ) from isIso_of_reflects_iso φ e.inverse
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_modulePullback_pullbackFst B S hS p _ fun W hW => ?_
  let a := pullback.fst p (chartToSpace B S hS Y' W)
  let ha := isEtale_pullbackFst_chartToSpace B S hS p W
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (pullback p (chartToSpace B S hS Y' W))))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS
    (pullback p (chartToSpace B S hS Y' W)).1 (pullback p (chartToSpace B S hS Y' W)).2)
  let eW := StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (pullback p (chartToSpace B S hS Y' W))))) (mTW W)
  have : (etaleModulePullback.{u, u} B S hS a ha).Additive :=
    etaleModulePullback_additive B S hS a ha
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteColimits_etaleModulePullback B S hS a ha
  have h₀ : IsIso ((smallEtaleDerivedModulePullback B S hS a).map (e.inverse.map φ)) := by
    have : IsIso (eW.functor.map ((smallEtaleDerivedModulePullback B S hS a).map
        (e.inverse.map φ))) := h W hW
    exact isIso_of_reflects_iso _ eW.functor
  have h₁ : IsIso ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.map
      (e.inverse.map φ)) :=
    (NatIso.isIso_map_iff (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha) _).1 h₀
  rw [DerivedCategory.isIso_iff] at h₁
  let φ' : (show DerivedCategory (Modules.{u, u} B S hS T.1 T.2) from e.inverse.obj K) ⟶
      (show DerivedCategory (Modules.{u, u} B S hS T.1 T.2) from e.inverse.obj L) :=
    e.inverse.map φ
  have h₂ : IsIso ((etaleModulePullback.{u, u} B S hS a ha).map
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS T.1 T.2) n).map φ')) :=
    (Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff
      (C₁ := Modules.{u, u} B S hS T.1 T.2)
      (C₂ := Modules.{u, u} B S hS (pullback p (chartToSpace B S hS Y' W)).1
        (pullback p (chartToSpace B S hS Y' W)).2)
      (etaleModulePullback.{u, u} B S hS a ha) φ' n).1 (h₁ n)
  exact (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS a ha) _).2 h₂

end Detection

section PseudoCoherent

/-- **Derived pullback preserves pseudo-coherence, at arbitrary models**: Stacks 08H4
(`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback`) read through the
comparisons of the models with the standard ones. -/
theorem isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels {X Y : AlgebraicSpaces B S hS}
    (g : X ⟶ Y)
    (mX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (mY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (E : @DerivedCategory _ _ _ mY)
    (hE : letI : HasDerivedCategory.{w'} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) := mY
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent E) :
    letI : HasDerivedCategory.{w} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) := mX
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((smallEtaleDerivedModulePullbackOfModels B S hS g mX mY).obj E) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  have i₁ := ((StacksDraft.DerivedModel.modelInverseCompQIso (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) mY).app K).symm ≪≫
    (StacksDraft.DerivedModel.modelEquiv _ mY).inverse.mapIso e
  obtain ⟨P, hP, ⟨e'⟩⟩ := isPseudoCoherent_smallEtaleDerivedModulePullback g _ ⟨K, hK, ⟨i₁⟩⟩
  have i₂ := ((StacksDraft.DerivedModel.modelCompQIso (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) mX).app P).symm ≪≫
    (StacksDraft.DerivedModel.modelEquiv _ mX).functor.mapIso e'
  exact ⟨P, hP, ⟨i₂⟩⟩

end PseudoCoherent


section Models

open Stacks.CategoryTheory.BaseChange MilnorPatching

/-- `Lf^*` read at arbitrary models commutes with the shifts: the comparisons of models
(`StacksDraft.Perfect.derivedEquivalenceCommShift`) and `Lf^*`
(`AlgebraicGeometry.Space.commShift_smallEtaleDerivedModulePullback`) do. -/
abbrev commShift_smallEtaleDerivedModulePullbackOfModels {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (mX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (mY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :=
  conjCommShift (smallEtaleStdModelEquiv Y mY) (smallEtaleStdModelEquiv X mX)
    (smallEtaleDerivedModulePullback B S hS f) (commShift_smallEtaleDerivedModulePullback B S hS f)
    (StacksDraft.Perfect.derivedEquivalenceCommShift (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) mY)
    (StacksDraft.Perfect.derivedEquivalenceCommShift (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) mX)

/-- `Lf^*` read at arbitrary models is triangulated: the comparisons of models
(`StacksDraft.Perfect.derivedEquivalence_isTriangulated`) and `Lf^*`
(`AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedModulePullback`) are. -/
theorem isTriangulated_smallEtaleDerivedModulePullbackOfModels {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (mX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (mY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    letI := mX
    letI := mY
    letI := commShift_smallEtaleDerivedModulePullbackOfModels f mX mY
    ((smallEtaleStdModelEquiv Y mY).inverse ⋙ smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleStdModelEquiv X mX).functor).IsTriangulated :=
  conjCommShift_isTriangulated (smallEtaleStdModelEquiv Y mY) (smallEtaleStdModelEquiv X mX)
    (smallEtaleDerivedModulePullback B S hS f)
    (isTriangulated_smallEtaleDerivedModulePullback B S hS f)
    (StacksDraft.Perfect.derivedEquivalence_isTriangulated (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) mY)
    (StacksDraft.Perfect.derivedEquivalence_isTriangulated (HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) mX)

end Models

section Step

variable (B S hS) in
/-- **The isomorphism step of Stacks 0DL7 for one triple.** For a commutative square
`i ≫ f' = f ≫ j` of algebraic spaces, models of the four derived categories and a triple
`(M, K', α)`: for every distinguished triangle `M' → Rj_* M ⊕ Rf'_* K' → Rj_* Rf_* Li^* K' → M'[1]`
whose second map is the glueing map (`AlgebraicGeometry.Space.pushoutGlueingMapOfModels`), the maps
`Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` adjoint to the two components of the first map are
isomorphisms. `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso` asks this of every
pseudo-coherent triple on a pushout. -/
def PushoutGlueingIsIsoStep {X X' Y Y' : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (f' : X' ⟶ Y') (j : Y ⟶ Y') (w : i ≫ f' = f ≫ j)
    (mY' : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
    (mY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (mX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (mX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (M : @DerivedCategory _ _ _ mY) (K' : @DerivedCategory _ _ _ mX')
    (α : (smallEtaleDerivedModulePullbackOfModels B S hS f mX mY).obj M ≅
      (smallEtaleDerivedModulePullbackOfModels B S hS i mX mX').obj K') : Prop :=
  ∀ {M' : @DerivedCategory _ _ _ mY'}
    (u : letI := mY'; M' ⟶ (smallEtaleDerivedModulePushforwardOfModels B S hS j mY mY').obj M ⊞
      (smallEtaleDerivedModulePushforwardOfModels B S hS f' mX' mY').obj K')
    (v : letI := mY'; (smallEtaleDerivedModulePushforwardOfModels B S hS j mY mY').obj
      ((smallEtaleDerivedModulePushforwardOfModels B S hS f mX mY).obj
        ((smallEtaleDerivedModulePullbackOfModels B S hS i mX mX').obj K')) ⟶ M'⟦(1 : ℤ)⟧),
    (letI := mY'; Pretriangulated.Triangle.mk u
      (pushoutGlueingMapOfModels i f f' j w mY' mY mX mX' M K' α.hom) v ∈
        distTriang (@DerivedCategory _ _ _ mY')) →
    IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS j mY mY').homEquiv _ _).symm
        (letI := mY'; u ≫ biprod.fst)) ∧
      IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS f' mX' mY').homEquiv _ _).symm
        (letI := mY'; u ≫ biprod.snd))

end Step

section Cube

open Stacks.CategoryTheory.BaseChange MilnorPatching

variable {Y' Y X X' W YW XW X'W : AlgebraicSpaces B S hS}
  (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y') (iW : XW ⟶ X'W) (fW : XW ⟶ YW)
  (f'W : X'W ⟶ W) (jW : YW ⟶ W) (h : W ⟶ Y') (hY : YW ⟶ Y) (hX : XW ⟶ X) (hX' : X'W ⟶ X')
  (w : i ≫ f' = f ≫ j) (wW : iW ≫ f'W = fW ≫ jW) (hi : hX ≫ i = iW ≫ hX')
  (sqj : IsPullback hY jW j h) (sqf : IsPullback hX fW f hY) (sqf' : IsPullback hX' f'W f' h)
  (hh : IsEtale B S hS h.hom)
  (mY' : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
  (mY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
  (mX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (mX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
  (mW : HasDerivedCategory.{t₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
  (mYW : HasDerivedCategory.{t₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS YW)))
  (mXW : HasDerivedCategory.{t₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS XW)))
  (mX'W : HasDerivedCategory.{t₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'W)))

include i f f' j iW fW f'W jW h hY hX hX' w wW hi sqj sqf sqf' hh mY' mY mX mX' mW mYW mXW mX'W in
/-- **The isomorphism step of Stacks 0DL7 is étale local, for algebraic spaces at arbitrary
models.** For a commutative square `i, f, f', j` and its base change `iW, fW, f'W, jW` along an
étale `h : W ⟶ Y'` (the faces of `j`, `f`, `f'` cartesian): if the isomorphism step holds for the
glueing map of the restricted triple, then for every distinguished triangle on the glueing map of
`(M, K', α)` the maps `Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` become isomorphisms after restriction.
This is `MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange` with the cube condition
`AlgebraicGeometry.Space.smallEtaleDerivedPullback_cube` and the canonical form of Stacks 08GE,
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap`. -/
theorem pushoutGlueingMap_isIso_restrict
    (M : @DerivedCategory _ _ _ mY) (K' : @DerivedCategory _ _ _ mX')
    (α : ((smallEtaleStdModelEquiv Y mY).inverse ⋙ smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleStdModelEquiv X mX).functor).obj M ≅
      ((smallEtaleStdModelEquiv X' mX').inverse ⋙ smallEtaleDerivedModulePullback B S hS i ⋙
        (smallEtaleStdModelEquiv X mX).functor).obj K') :
    letI := mY'
    letI := mW
    type_of% (MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange_iso
    (smallEtaleStdModelEquiv Y' mY') (smallEtaleStdModelEquiv Y mY)
    (smallEtaleStdModelEquiv X' mX') (smallEtaleStdModelEquiv X mX)
    (smallEtaleStdModelEquiv W mW) (smallEtaleStdModelEquiv YW mYW)
    (smallEtaleStdModelEquiv X'W mX'W) (smallEtaleStdModelEquiv XW mXW)
    (smallEtaleDerivedModuleAdjunction B S hS j) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS i)
    (smallEtaleDerivedModuleAdjunction B S hS jW) (smallEtaleDerivedModuleAdjunction B S hS f'W)
    (smallEtaleDerivedModuleAdjunction B S hS fW) (smallEtaleDerivedModuleAdjunction B S hS iW)
    (hΦs := commShift_smallEtaleDerivedModulePullbackOfModels h mW mY')
    (hΦt := isTriangulated_smallEtaleDerivedModulePullbackOfModels h mW mY')
    (smallEtaleDerivedModulePullbackCompIso B S hS f j)
    (smallEtaleDerivedModulePullbackCongr B S hS w.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS i f')
    (smallEtaleDerivedModulePullbackCompIso B S hS fW jW)
    (smallEtaleDerivedModulePullbackCongr B S hS wW.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW f'W)
    (smallEtaleDerivedModulePullbackCompIso B S hS jW h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS j h jW hY sqj.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS fW hY)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f hY fW hX sqf.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS f'W h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f' h f'W hX' sqf'.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW hX')
    (smallEtaleDerivedModulePullbackSquareIso B S hS i hX' iW hX hi)
    (fun N ↦ smallEtaleDerivedPullback_cube i f f' j iW fW f'W jW h hY hX hX' w wW sqj.w sqf.w
      sqf'.w hi N)
    (isIso_smallEtaleDerivedModuleBaseChangeMap j h jW hY sqj hh)
    (isIso_smallEtaleDerivedModuleBaseChangeMap f hY fW hX sqf
      (isEtale_of_isPullback B S hS _ _ _ _ sqj.flip hh))
    (isIso_smallEtaleDerivedModuleBaseChangeMap f' h f'W hX' sqf' hh)
    M K' α (hΦ := additive_smallEtaleDerivedModulePullbackOfModels h mW mY')) :=
  let := mY'
  let := mW
  (MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange_iso
    (smallEtaleStdModelEquiv Y' mY') (smallEtaleStdModelEquiv Y mY)
    (smallEtaleStdModelEquiv X' mX') (smallEtaleStdModelEquiv X mX)
    (smallEtaleStdModelEquiv W mW) (smallEtaleStdModelEquiv YW mYW)
    (smallEtaleStdModelEquiv X'W mX'W) (smallEtaleStdModelEquiv XW mXW)
    (smallEtaleDerivedModuleAdjunction B S hS j) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS i)
    (smallEtaleDerivedModuleAdjunction B S hS jW) (smallEtaleDerivedModuleAdjunction B S hS f'W)
    (smallEtaleDerivedModuleAdjunction B S hS fW) (smallEtaleDerivedModuleAdjunction B S hS iW)
    (hΦs := commShift_smallEtaleDerivedModulePullbackOfModels h mW mY')
    (hΦt := isTriangulated_smallEtaleDerivedModulePullbackOfModels h mW mY')
    (smallEtaleDerivedModulePullbackCompIso B S hS f j)
    (smallEtaleDerivedModulePullbackCongr B S hS w.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS i f')
    (smallEtaleDerivedModulePullbackCompIso B S hS fW jW)
    (smallEtaleDerivedModulePullbackCongr B S hS wW.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW f'W)
    (smallEtaleDerivedModulePullbackCompIso B S hS jW h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS j h jW hY sqj.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS fW hY)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f hY fW hX sqf.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS f'W h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f' h f'W hX' sqf'.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW hX')
    (smallEtaleDerivedModulePullbackSquareIso B S hS i hX' iW hX hi)
    (fun N ↦ smallEtaleDerivedPullback_cube i f f' j iW fW f'W jW h hY hX hX' w wW sqj.w sqf.w
      sqf'.w hi N)
    (isIso_smallEtaleDerivedModuleBaseChangeMap j h jW hY sqj hh)
    (isIso_smallEtaleDerivedModuleBaseChangeMap f hY fW hX sqf
      (isEtale_of_isPullback B S hS _ _ _ _ sqj.flip hh))
    (isIso_smallEtaleDerivedModuleBaseChangeMap f' h f'W hX' sqf' hh)
    M K' α (hΦ := additive_smallEtaleDerivedModulePullbackOfModels h mW mY'))

include i f f' j iW fW f'W jW h hY hX hX' w wW hi sqj sqf sqf' hh mY' mY mX mX' mW mYW mXW mX'W in
/-- **The isomorphism step of Stacks 0DL7 is étale local**, in the shape of
`AlgebraicGeometry.Space.PushoutGlueingIsIsoStep`: if the isomorphism step holds on the
base-changed square for the restrictions of `M` and `K'` and every isomorphism `αW` between their
inverse images, then for every distinguished triangle on the glueing map of `(M, K', α)` the maps
`Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` become isomorphisms after restriction along `YW ⟶ Y` and
`X'W ⟶ X'`. -/
theorem isIso_restrict_of_pushoutGlueingIsIsoStep
    (M : @DerivedCategory _ _ _ mY) (K' : @DerivedCategory _ _ _ mX')
    (α : (smallEtaleDerivedModulePullbackOfModels B S hS f mX mY).obj M ≅
      (smallEtaleDerivedModulePullbackOfModels B S hS i mX mX').obj K')
    (hA : ∀ αW : (smallEtaleDerivedModulePullbackOfModels B S hS fW mXW mYW).obj
        ((smallEtaleDerivedModulePullbackOfModels B S hS hY mYW mY).obj M) ≅
        (smallEtaleDerivedModulePullbackOfModels B S hS iW mXW mX'W).obj
          ((smallEtaleDerivedModulePullbackOfModels B S hS hX' mX'W mX').obj K'),
      PushoutGlueingIsIsoStep B S hS iW fW f'W jW wW mW mYW mXW mX'W
        ((smallEtaleDerivedModulePullbackOfModels B S hS hY mYW mY).obj M)
        ((smallEtaleDerivedModulePullbackOfModels B S hS hX' mX'W mX').obj K') αW)
    {M' : @DerivedCategory _ _ _ mY'}
    (u : letI := mY'; M' ⟶ (smallEtaleDerivedModulePushforwardOfModels B S hS j mY mY').obj M ⊞
      (smallEtaleDerivedModulePushforwardOfModels B S hS f' mX' mY').obj K')
    (v : letI := mY'; (smallEtaleDerivedModulePushforwardOfModels B S hS j mY mY').obj
      ((smallEtaleDerivedModulePushforwardOfModels B S hS f mX mY).obj
        ((smallEtaleDerivedModulePullbackOfModels B S hS i mX mX').obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : letI := mY'; Pretriangulated.Triangle.mk u
      (pushoutGlueingMapOfModels i f f' j w mY' mY mX mX' M K' α.hom) v ∈
        distTriang (@DerivedCategory _ _ _ mY')) :
    IsIso ((smallEtaleDerivedModulePullbackOfModels B S hS hY mYW mY).map
        (((smallEtaleDerivedModuleAdjunctionOfModels B S hS j mY mY').homEquiv _ _).symm
          (letI := mY'; u ≫ biprod.fst))) ∧
      IsIso ((smallEtaleDerivedModulePullbackOfModels B S hS hX' mX'W mX').map
        (((smallEtaleDerivedModuleAdjunctionOfModels B S hS f' mX' mY').homEquiv _ _).symm
          (letI := mY'; u ≫ biprod.snd))) :=
  pushoutGlueingMap_isIso_restrict i f f' j iW fW f'W jW h hY hX hX' w wW hi sqj sqf sqf' hh mY'
    mY mX mX' mW mYW mXW mX'W M K' α (fun αW _ uW vW hW ↦ hA αW uW vW hW) u v hT

end Cube

section Reduction

variable (B S hS) in
/-- **The isomorphism step of Stacks 0DL7 on an affine étale chart.** For the pushout
`Y' = Y ⨿_X X'` of a thickening `i` and an affine morphism `f` of algebraic spaces over `S`, an
étale chart `W ⟶ Y'` with affine underlying scheme over which `X' ⟶ Y'` is affine (so that
`X' ×_{Y'} W` is affine), and pseudo-coherent `M` on `Y ×_{Y'} W` and `K'` on `X' ×_{Y'} W`: the
isomorphism step (`AlgebraicGeometry.Space.PushoutGlueingIsIsoStep`) holds for the base change of
the square along `W ⟶ Y'` (`AlgebraicGeometry.Space.chartCubeI`), at any models and for every
`α : LfW^* M ≅ LiW^* K'`. This is the affine case of the proof of Stacks 0DL7, where the source
passes to rings. It is a statement, not a theorem. -/
def DerivedPushoutGlueingIsIsoOnAffineChart : Prop :=
  ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
    IsThickeningHom B S hS i → IsAffineHom B S hS f.hom → ∀ [HasPushout i f]
    (W : SmallEtale B S hS (pushout i f).obj), IsAffineChart B S hS (pushout i f).obj W →
    IsAffineHom B S hS
      (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).hom →
    ∀ (mW : HasDerivedCategory.{t₁} (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (chartSpace B S hS (pushout i f) W))))
      (mYW : HasDerivedCategory.{t₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))))
      (mXW : HasDerivedCategory.{t₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (chartCubeX f (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))))
      (mX'W : HasDerivedCategory.{t₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)))))
      (M : @DerivedCategory _ _ _ mYW) (K' : @DerivedCategory _ _ _ mX'W),
      (letI : HasDerivedCategory.{t₂} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS
            (pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)).1
            (pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)).2).O)) := mYW;
        (smallEtaleRingedSite B S hS
          (pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)).1
          (pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)).2).IsPseudoCoherent
            M) →
      (letI : HasDerivedCategory.{t₄} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS
            (pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).1
            (pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).2).O)) := mX'W;
        (smallEtaleRingedSite B S hS
          (pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).1
          (pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).2).IsPseudoCoherent
            K') →
      ∀ α : (smallEtaleDerivedModulePullbackOfModels B S hS
          (pullback.snd f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
          mXW mYW).obj M ≅
        (smallEtaleDerivedModulePullbackOfModels B S hS
          (chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
            (chartToSpace B S hS (pushout i f) W)) mXW mX'W).obj K',
      PushoutGlueingIsIsoStep B S hS
        (chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
          (chartToSpace B S hS (pushout i f) W))
        (pullback.snd f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
        (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
        (pullback.snd (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
        (chartCubeI_snd i f (pushout.inl i f) (pushout.inr i f) pushout.condition
          (chartToSpace B S hS (pushout i f) W)) mW mYW mXW mX'W M K' α

/-- **The isomorphism step of Stacks 0DL7 from its affine case.** The isomorphism step
`AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso` follows from its case on the affine étale
charts of the pushout, `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIsoOnAffineChart` (at the
standard models), given that `X' ⟶ Y'` is affine (`hinl`; the proof of Stacks 07VX gives it, its
statement does not). As in the source: whether `Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` are isomorphisms
may be checked after restriction to `Y ×_{Y'} W` and `X' ×_{Y'} W` for the affine étale charts `W`
of `Y'`
(`isIso_of_forall_isIso_smallEtaleDerivedModulePullbackOfModels_pullbackFst`);
restriction carries the glueing map to the glueing map of the restricted triple
(`AlgebraicGeometry.Space.isIso_restrict_of_pushoutGlueingIsIsoStep`), whose terms stay
pseudo-coherent
(`AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels`). -/
theorem derivedPushoutGlueingIsIso_of_onAffineChart
    (hA : DerivedPushoutGlueingIsIsoOnAffineChart.{u + 1, u + 1, u + 1, u + 1, u} B S hS)
    (hinl : ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
      IsThickeningHom B S hS i → IsAffineHom B S hS f.hom → ∀ [HasPushout i f],
        IsAffineHom B S hS (pushout.inl i f).hom) :
    DerivedPushoutGlueingIsIso.{w₁, w₂, w₃, w₄, u} B S hS := by
  intro X X' Y i f hi hf _ hY' hY hX hX' M K' hM hK' α M' u v hT
  have key : ∀ W : SmallEtale B S hS (pushout i f).obj, IsAffineChart B S hS (pushout i f).obj W →
      _ := fun W hW ↦ isIso_restrict_of_pushoutGlueingIsIsoStep i f (pushout.inl i f)
    (pushout.inr i f)
    (chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      (chartToSpace B S hS (pushout i f) W))
    (pullback.snd f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
    (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
    (pullback.snd (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
    (chartToSpace B S hS (pushout i f) W)
    (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
    (pullback.fst f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
    (pullback.fst (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
    pushout.condition
    (chartCubeI_snd i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      (chartToSpace B S hS (pushout i f) W))
    (chartCubeI_fst i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      (chartToSpace B S hS (pushout i f) W))
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) (isEtale_chartToSpace B S hS _ W) hY' hY hX hX'
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) M K' α
    (fun αW ↦ hA i f hi hf W hW
      (isAffineHom_of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _)) (hinl i f hi hf))
      _ _ _ _ _ _
      (isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels _ _ hY M hM)
      (isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels _ _ hX' K' hK') αW) u v hT
  exact ⟨isIso_of_forall_isIso_smallEtaleDerivedModulePullbackOfModels_pullbackFst
      (pushout.inr i f) hY (fun _ ↦ HasDerivedCategory.standard _) _ fun W hW ↦ (key W hW).1,
    isIso_of_forall_isIso_smallEtaleDerivedModulePullbackOfModels_pullbackFst
      (pushout.inl i f) hX' (fun _ ↦ HasDerivedCategory.standard _) _ fun W hW ↦ (key W hW).2⟩

/-- **Stacks 0DL7 from its affine case.** The essential image statement
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage` follows from the isomorphism step on the
affine étale charts of the pushout
(`AlgebraicGeometry.Space.DerivedPushoutGlueingIsIsoOnAffineChart`) and the affineness of
`X' ⟶ Y'`. -/
theorem derivedPushoutEssentialImage_of_onAffineChart
    (hA : DerivedPushoutGlueingIsIsoOnAffineChart.{u + 1, u + 1, u + 1, u + 1, u} B S hS)
    (hinl : ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
      IsThickeningHom B S hS i → IsAffineHom B S hS f.hom → ∀ [HasPushout i f],
        IsAffineHom B S hS (pushout.inl i f).hom) :
    DerivedPushoutEssentialImage.{w₁, w₂, w₃, w₄, u} B S hS :=
  derivedPushoutEssentialImage_of_derivedPushoutGlueingIsIso B S hS
    (derivedPushoutGlueingIsIso_of_onAffineChart hA hinl)

end Reduction

end AlgebraicGeometry.Space

end

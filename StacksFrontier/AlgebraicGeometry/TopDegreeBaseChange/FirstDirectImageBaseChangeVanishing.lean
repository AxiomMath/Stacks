module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohInduction.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.RingBaseCriterion
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# Base change of `R¹ f_* 𝒪_X`, read on vanishing

The proofs of [Stacks, Tags 0E7F, 0E7G] and [0E7H] quote conclusion (b)/(c) of
[Stacks, Tag 0EX3] (made available by [Stacks, Tag 0E7D] part (2)) for the structure sheaf in
degree one: the formation of `R¹ f_* 𝒪_X` commutes with base change, for `f` proper with fibres
of dimension at most one. Every use the source makes of it is the transport of a *vanishing*:
from `H¹(X_y, 𝒪_{X_y}) = 0` to the vanishing of the pullback of `R¹ f_* 𝒪_X` to `Spec κ(y)`, and
from `R¹ f_* 𝒪_X|_V = 0` to `R¹ f'_* 𝒪_{X'} = 0` after a base change `Y' ⟶ V`. This file proves
that transport in both directions, for an arbitrary base change.

Over an affine base `S` and an affine `S'`, the source's computation is the chain

`H¹(X', 𝒪_{X'}) = H¹(X, h'_* 𝒪_{X'}) = H¹(X, f^* (u_* 𝒪_{S'})) = H¹(X, 𝒪_X) ⊗_{Γ(S)} Γ(S')`

by [Stacks, Tag 089W] along the affine projection `h' : X' ⟶ X`, [Stacks, Tag 02KG] for the
affine morphism `u : S' ⟶ S`, [Stacks, Tag 01I9] and the affine case of [Stacks, Tag 0EX3] (b)
(the Eilenberg–Watts statement of `EilenbergWattsUnitor.lean`), whose top-degree vanishing
hypothesis is [Stacks, Tag 0E7D]. On the other side, the sections of the pullback of
`R¹ f_* 𝒪_X` over `S'` are `Γ(S, R¹ f_* 𝒪_X) ⊗_{Γ(S)} Γ(S')`
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`) and `Γ(S, R¹ f_* 𝒪_X) = H¹(X, 𝒪_X)` by
[Stacks, Tag 01XK]. Both sides are local on `Y'`, which globalises the comparison.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_cohomologyOne_pullback_iff_of_isAffine`: over affine schemes,
  `H¹(X', 𝒪_{X'}) = 0` if and only if `H¹(X, 𝒪_X) ⊗_{Γ(S)} Γ(S') = 0`.
* `isZero_pullback_firstDirectImage_iff_of_isAffine`: the same, as the vanishing of the pullback
  of `R¹ f_* 𝒪_X` against that of `R¹ q_* 𝒪_{X'}`.
* `isZero_pullback_firstDirectImage_iff_of_isPullback`: for an arbitrary cartesian square, with
  `f` quasi-compact and quasi-separated and `H²` vanishing over the affine opens of the base.
* `isZero_pullback_firstDirectImage_iff`: for `f` proper with fibres of dimension at most one and
  an arbitrary `g : Y' ⟶ Y`, `g^* R¹ f_* 𝒪_X = 0` if and only if `R¹ f'_* 𝒪_{X'} = 0`.

## Implementation notes

Only the vanishing is transported, not an isomorphism of sheaves on `Y'`: a global isomorphism
needs the canonical comparison map of [Stacks, Tag 0EX3] (c) and its compatibility with
restriction to opens, while every consumer in the source uses the clause only through the
vanishing, which is local on `Y'` and is computed over affines with no canonical map at all.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

section SpecBase

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {R : Type u} [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-- `H¹(X, 𝒪_X)` for a scheme `X` over `Spec R`, as an `R`-module. -/
abbrev cohomologyOneOver : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
    ((qcohCohomology W.left 1).obj
      ⟨SheafOfModules.unit W.left.ringCatSheaf,
        AffineQcohPushforward.isQuasicoherent_unit W.left⟩)

/-- **The top cohomology of the structure sheaf after an affine base change, over `Spec R`,
read on vanishing.** For `X` over `Spec R` with `H²(X, -) = 0` on quasi-coherent modules and
`X'` its base change along `Spec φ : Spec B ⟶ Spec R`, `H¹(X', 𝒪_{X'}) = 0` if and only if
`H¹(X, 𝒪_X) ⊗_R B = 0`. -/
theorem isZero_cohomologyOne_pullback_iff [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections W.left).rightDerivedPlus
        (((1 : ℕ) : ℤ) + 1)).obj G))
    {B : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ B) {X' : Scheme.{u}} (q : X' ⟶ Spec B)
    (h' : X' ⟶ W.left) (sq : IsPullback q h' (Spec.map φ) W.hom) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) ↔
      IsZero (MonoidalCategory.tensorObj (cohomologyOneOver W)
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B))) := by
  have _ : IsAffineHom h' := MorphismProperty.of_isPullback (P := @IsAffineHom) sq
    inferInstance
  let UB : (Spec B).Modules := SheafOfModules.unit (Spec B).ringCatSheaf
  have _ : UB.IsQuasicoherent := AffineQcohPushforward.isQuasicoherent_unit _
  let O' : X'.Modules := SheafOfModules.unit X'.ringCatSheaf
  have _ : O'.IsQuasicoherent := AffineQcohPushforward.isQuasicoherent_unit _
  -- Step 1: Tag 089W along the affine `h'`.
  have h1 :
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerived 1).obj O') ↔
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections W.left).rightDerived 1).obj
        ((Scheme.Modules.pushforward h').obj O')) := by
    rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff h'.appTop.hom]
    exact (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward h' O' 1).isZero_iff
  -- Step 2: Tag 02KG, `h'_* 𝒪_{X'} ≅ W^* (Spec φ)_* 𝒪_{Spec B}`.
  have _ : IsIso ((AffinePushforward.baseChangeNatTrans sq.w).app UB) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom sq UB
  let e2 : (Scheme.Modules.pushforward h').obj O' ≅
      (Scheme.Modules.pullback W.hom).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj UB) :=
    (Scheme.Modules.pushforward h').mapIso (Scheme.Modules.pullbackUnitIso q).symm ≪≫
      (asIso ((AffinePushforward.baseChangeNatTrans sq.w).app UB)).symm
  -- Step 3: Tag 01I9, `(Spec φ)_* 𝒪_{Spec B} ≅ (B_R)~`.
  let M : ModuleCat.{u} R := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)
  let e3 : (Scheme.Modules.pushforward (Spec.map φ)).obj UB ≅ (tilde.functor _).obj M :=
    (pushforwardTildeIso (CommRingCat.of R) B φ).app (ModuleCat.of B B)
  -- Step 4: the unitor `𝒪 ⊗ G ≅ G`.
  let G : W.left.Modules := (Scheme.Modules.pullback W.hom).obj ((tilde.functor _).obj M)
  let e4 : (geometricFactorFormula R W (SheafOfModules.unit W.left.ringCatSheaf)).obj M ≅ G :=
    (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso W.left.presheaf
      (ringSheafCond W.left)).app G
  -- Step 5: Eilenberg-Watts.
  let F : (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit W.left.ringCatSheaf, AffineQcohPushforward.isQuasicoherent_unit W.left⟩
  let e5 := (affineTopDegreeTensorCohomologyIso R W 1 F hvan).app M
  let H := (Stacks.Cohomology.AffineBase.moduleGlobalSections W.left).rightDerived 1
  have h5 : IsZero (MonoidalCategory.tensorObj (cohomologyOneOver W) M) ↔ IsZero (H.obj G) := by
    rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff
      (algebraMap R Γ(W.left, ⊤)) (H.obj G)]
    let e : (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj (H.obj G) ≅
        (affineTopDegreeFunctor R W 1 (geometricFactor R W F)).obj M :=
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).mapIso (H.mapIso e4.symm)
    exact (e5 ≪≫ e.symm).isZero_iff
  rw [h1, h5]
  exact (H.mapIso (e2 ≪≫ (Scheme.Modules.pullback W.hom).mapIso e3)).isZero_iff

/-- **The top cohomology of the structure sheaf after an affine base change, over an affine
scheme, read on vanishing.** Let `f : X ⟶ S` be quasi-compact and quasi-separated onto an affine
scheme with `H²(X, -) = 0` on quasi-coherent modules, and let `X'` be the base change of `X`
along a morphism `u : S' ⟶ S` from an affine scheme. Then `H¹(X', 𝒪_{X'}) = 0` if and only if
`H¹(X, 𝒪_X) ⊗_{Γ(S)} Γ(S') = 0`. -/
theorem isZero_cohomologyOne_pullback_iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [QuasiCompact f] [QuasiSeparated f]
    (hvan : ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus 2).obj G))
    {S' X' : Scheme.{u}} [IsAffine S'] (u : S' ⟶ S) (q : X' ⟶ S') (h' : X' ⟶ X)
    (sq : IsPullback q h' u f) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) ↔
      IsZero (MonoidalCategory.tensorObj
        ((ModuleCat.restrictScalars f.appTop.hom).obj
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
            (SheafOfModules.unit X.ringCatSheaf)))
        ((ModuleCat.restrictScalars u.appTop.hom).obj (ModuleCat.of Γ(S', ⊤) Γ(S', ⊤)))) := by
  let W : Over (Spec (CommRingCat.of Γ(S, ⊤))) := Over.mk (f ≫ S.isoSpec.hom)
  have _ : QuasiCompact W.hom := inferInstanceAs (QuasiCompact (f ≫ S.isoSpec.hom))
  have _ : QuasiSeparated W.hom := inferInstanceAs (QuasiSeparated (f ≫ S.isoSpec.hom))
  have sq' : IsPullback (q ≫ S'.isoSpec.hom) h' (Spec.map u.appTop) W.hom :=
    sq.of_iso (Iso.refl _) S'.isoSpec (Iso.refl _) S.isoSpec (by simp) (by simp)
      (Scheme.isoSpec_hom_naturality u).symm (by simp [W])
  have hvan' : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections W.left).rightDerivedPlus
        (((1 : ℕ) : ℤ) + 1)).obj G) := by
    rw [show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num]
    exact hvan
  refine (isZero_cohomologyOne_pullback_iff W hvan' u.appTop (q ≫ S'.isoSpec.hom) h' sq').trans ?_
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := baseSectionsAlgebra Γ(S, ⊤) W
  have hring : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom := by
    have := Stacks.AlgebraicGeometry.TopDegreeFiniteType.ΓSpecIso_inv_comp_isoSpec_appTop f
    show baseRingToSections _ W (op ⊤) = f.appTop.hom
    simp only [baseRingToSections]
    rw [← this]
    have hle : (Opens.leTop (⊤ : X.Opens)) = 𝟙 _ := Subsingleton.elim _ _
    simp only [W, Over.mk_hom, hle, op_id, CategoryTheory.Functor.map_id]
    rfl
  exact (MonoidalCategory.tensorIso ((ModuleCat.restrictScalarsCongr hring).app
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)))
    (Iso.refl ((ModuleCat.restrictScalars u.appTop.hom).obj
      (ModuleCat.of Γ(S', ⊤) Γ(S', ⊤))))).isZero_iff

end SpecBase

/-- An extension of scalars `B ⊗_A M` vanishes exactly when `M ⊗_A B` does. -/
theorem isZero_extendScalars_iff_isZero_tensorObj {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) (M : ModuleCat.{u} A) :
    IsZero ((ModuleCat.extendScalars ψ).obj M) ↔
      IsZero (MonoidalCategory.tensorObj M
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of B B))) := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact (TensorProduct.comm A
    ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of B B)) M).toEquiv.subsingleton_congr

/-- **Over affine schemes, the pullback of `R¹ f_* 𝒪_X` vanishes exactly when the first higher
direct image of the structure sheaf of the base change does.** Here `f : X ⟶ S` is
quasi-compact and quasi-separated onto an affine scheme with `H²(X, -) = 0` on quasi-coherent
modules, and `q : X' ⟶ S'` is its base change along a morphism `u : S' ⟶ S` from an affine
scheme. -/
theorem isZero_pullback_firstDirectImage_iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [QuasiCompact f] [QuasiSeparated f]
    (hvan : ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus 2).obj G))
    {S' X' : Scheme.{u}} [IsAffine S'] (u : S' ⟶ S) (q : X' ⟶ S') (h' : X' ⟶ X)
    (sq : IsPullback q h' u f) :
    IsZero ((Scheme.Modules.pullback u).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf q) := by
  have _ : QuasiCompact q := MorphismProperty.of_isPullback (P := @QuasiCompact) sq.flip
    inferInstance
  have _ : QuasiSeparated q := MorphismProperty.of_isPullback (P := @QuasiSeparated) sq.flip
    inferInstance
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have _ : O.IsQuasicoherent := AffineQcohPushforward.isQuasicoherent_unit X
  let O' : X'.Modules := SheafOfModules.unit X'.ringCatSheaf
  have _ : O'.IsQuasicoherent := AffineQcohPushforward.isQuasicoherent_unit _
  let P : S.Modules := firstDirectImageStructureSheaf f
  have _ : P.IsQuasicoherent :=
    Tag01XJQcohInduction.higherDirectImage_isQuasicoherent f O 1
  have _ : ((Scheme.Modules.pullback u).obj P).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback u P
  -- the right-hand side, through Tag 01XK over the affine `S'`
  have hR : IsZero (firstDirectImageStructureSheaf q) ↔
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerived
        1).obj O') := by
    rw [← isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward q 1 O',
      Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (show (1 : ℤ) = ((1 : ℕ) : ℤ) by
        norm_num)]
  rw [hR, isZero_cohomologyOne_pullback_iff_of_isAffine f hvan u q h' sq,
    ← isZero_extendScalars_iff_isZero_tensorObj]
  -- the left-hand side, through global sections over the affine `S'`
  have hsec : IsZero ((Scheme.Modules.pullback u).obj P) ↔
      IsZero ((_root_.SheafOfModules.evaluation S'.ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.pullback u).obj P)) :=
    ⟨fun h => Functor.map_isZero _ h, fun h => isZero_of_isZero_sections_of_isAffine _ h⟩
  have hle : (⊤ : S'.Opens) ≤ u ⁻¹ᵁ ⊤ := le_top
  let e1 := affinePullbackSectionsBaseChangeIso u P (isAffineOpen_top S) (isAffineOpen_top S') hle
  have happ : u.appLE ⊤ ⊤ hle = u.appTop := Scheme.Hom.appLE_eq_app u
  -- Tag 01XK over the affine `S`
  let A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨O, inferInstance⟩
  let e2 : (ModuleCat.restrictScalars f.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj O) ≅
      ModuleCat.of Γ(S, ⊤) Γ(P, ⊤) :=
    (ModuleCat.restrictScalars f.appTop.hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.AffineBase.moduleGlobalSections X) 1).app O) ≪≫
    (cohomologyIsoGlobalSectionsRightDerivedPushforward f ((1 : ℕ) : ℤ)).app A
  have h1 : IsZero ((_root_.SheafOfModules.evaluation S'.ringCatSheaf (op ⊤)).obj
      ((Scheme.Modules.pullback u).obj P)) ↔
      IsZero ((ModuleCat.extendScalars (u.appLE ⊤ ⊤ hle).hom).obj
        (ModuleCat.of Γ(S, ⊤) Γ(P, ⊤))) := by
    rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
    exact e1.toLinearEquiv.toEquiv.subsingleton_congr.symm
  rw [hsec, h1, happ]
  exact ((ModuleCat.extendScalars u.appTop.hom).mapIso e2).isZero_iff.symm

/-- `R¹ (f ∣_ V)_* 𝒪` is the restriction of `R¹ f_* 𝒪_X` to `V` ([Stacks, Tag 01E5]). -/
def firstDirectImageRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    firstDirectImageStructureSheaf (f ∣_ V) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f) :=
  (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus 1).mapIso
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ V).ι)).symm ≪≫
    SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V 1
      (SheafOfModules.unit X.ringCatSheaf)

/-- **The local form of `isZero_pullback_firstDirectImage_iff_of_isPullback`.** For a cartesian
square and affine opens `U` of `Y` and `V ⊆ g⁻¹(U)` of `Y'`, the restriction to `V` of the
pullback of `R¹ f_* 𝒪_X` vanishes exactly when that of `R¹ f'_* 𝒪_{X'}` does. -/
private theorem isZero_restrict_pullback_firstDirectImage_iff_of_isAffineOpen
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U) {V : Y'.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (hvan : ∀ G : (f ⁻¹ᵁ U).toScheme.Modules, G.IsQuasicoherent →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (f ⁻¹ᵁ U).toScheme).rightDerivedPlus 2).obj G)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f))) ↔
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f')) := by
  have _ : IsAffine (U : Scheme) := hU
  have _ : IsAffine (V : Scheme) := hV
  let UX := f ⁻¹ᵁ U
  let UY := f' ⁻¹ᵁ V
  have hsub : UY ≤ g' ⁻¹ᵁ UX := by
    show f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U)
    calc
      _ ≤ f' ⁻¹ᵁ (g ⁻¹ᵁ U) := f'.preimage_mono hVU
      _ = g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by simp only [← Scheme.Hom.comp_preimage, sq.w]
  let gV : (V : Scheme) ⟶ (U : Scheme) := g.resLE U V hVU
  have hres : IsPullback (g'.resLE UX UY hsub) (f' ∣_ V) (f ∣_ U) gV := by
    have h := Scheme.Hom.isPullback_resLE sq (US := U) (UT := V) (UX := UX) (UY := UY)
      (hUST := hVU) (hUSX := le_rfl) (hUY := (inf_eq_right.mpr hsub).symm)
    rwa [show f' ∣_ V = f'.resLE V UY le_rfl from
        (Scheme.Hom.resLE_eq_morphismRestrict f' (U := V)).symm,
      show f ∣_ U = f.resLE U UX le_rfl from
        (Scheme.Hom.resLE_eq_morphismRestrict f (U := U)).symm]
  let P := firstDirectImageStructureSheaf f
  let eL : (Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pullback g).obj P) ≅
      (Scheme.Modules.pullback gV).obj (firstDirectImageStructureSheaf (f ∣_ U)) :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp V.ι g).app P ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι g hVU).symm).app P ≪≫
      ((Scheme.Modules.pullbackComp gV U.ι).app P).symm ≪≫
      (Scheme.Modules.pullback gV).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app P).symm ≪≫
      (Scheme.Modules.pullback gV).mapIso (firstDirectImageRestrictIso f U).symm
  exact eL.isZero_iff.trans ((isZero_pullback_firstDirectImage_iff_of_isAffine (f ∣_ U) hvan gV
    (f' ∣_ V) (g'.resLE UX UY hsub) hres.flip).trans (firstDirectImageRestrictIso f' V).isZero_iff)

/-- **The pullback of `R¹ f_* 𝒪_X` along an arbitrary base change vanishes exactly when the
first higher direct image of the structure sheaf of the base change does.** Here `f` is
quasi-compact and quasi-separated and `H²(f⁻¹(U), -)` vanishes on quasi-coherent modules for
every affine open `U` of the base.

Both sides are local on `Y'`. Over an affine open `V ⊆ Y'` mapping into an affine open `U ⊆ Y`
the restriction of the left-hand side is the pullback of `R¹ (f ∣_ U)_* 𝒪` along `V ⟶ U`, the
restriction of the right-hand side is `R¹ (f' ∣_ V)_* 𝒪`, and the square restricts to a cartesian
square ([Stacks, Tag 01E5] and `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`); there the
statement is `isZero_pullback_firstDirectImage_iff_of_isAffine`. -/
theorem isZero_pullback_firstDirectImage_iff_of_isPullback {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (hvan : ∀ U : Y.Opens, IsAffineOpen U → ∀ G : (f ⁻¹ᵁ U).toScheme.Modules,
      G.IsQuasicoherent →
        IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (f ⁻¹ᵁ U).toScheme).rightDerivedPlus 2).obj G)) :
    IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf f') := by
  choose U hU hgU _ using fun y' : Y' =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := g.base y') (U := ⊤) (by simp)
  choose V hV hyV hVU using fun y' : Y' =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y') (U := g ⁻¹ᵁ U y') (hgU y')
  have hcover : ⨆ y' : Y', V y' = ⊤ :=
    le_antisymm le_top fun y _ => Opens.mem_iSup.mpr ⟨y, hyV y⟩
  have hloc (y' : Y') := isZero_restrict_pullback_firstDirectImage_iff_of_isAffineOpen sq (hU y')
    (hV y') (hVU y') (hvan _ (hU y'))
  have hcov (M : Y'.Modules) :
      IsZero M ↔ ∀ y', IsZero ((Scheme.Modules.restrictFunctor (V y').ι).obj M) :=
    ⟨fun h y' => Functor.map_isZero _ h, isZero_of_isZero_restrict_cover V hcover M⟩
  rw [hcov, hcov]
  exact forall_congr' hloc

/-- **The base-change clause of [Stacks, Tag 0EX3] for `R¹ f_* 𝒪_X`, read on vanishing.** For a
proper morphism `f : X ⟶ Y` all of whose fibres have dimension at most one and an arbitrary
morphism `g : Y' ⟶ Y`, the pullback of `R¹ f_* 𝒪_X` along `g` vanishes if and only if
`R¹ f'_* 𝒪_{X'} = 0` for the base change `f' : X ×_Y Y' ⟶ Y'`. -/
theorem isZero_pullback_firstDirectImage_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) ↔
      IsZero (firstDirectImageStructureSheaf (pullback.snd f g)) :=
  isZero_pullback_firstDirectImage_iff_of_isPullback (IsPullback.of_hasPullback f g)
    fun U hU G hG => by
      have _ : IsAffine U.toScheme := hU
      exact isZero_cohomology_of_affine_base (d := 1) (f ∣_ U)
        (topologicalKrullDim_fiber_morphismRestrict_le f U 1 fun t _ => hdim t) G 2
        (by norm_num)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

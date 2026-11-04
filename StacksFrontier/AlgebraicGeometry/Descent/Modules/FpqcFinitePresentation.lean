module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Descent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Finite presentation descends along fpqc coverings

A quasi-coherent module on a scheme is of finite presentation when its pullback to every member
of an fpqc covering is of finite presentation.

## Main results

* `AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`: finite presentation of a
  quasi-coherent module descends from an fpqc covering.

## Implementation notes

An fpqc family is represented by a cover for `AlgebraicGeometry.Scheme.fpqcPrecoverage`, and
pullback of modules is the functor `AlgebraicGeometry.Scheme.Modules.pullback`.

The statement is local on the base, so it suffices to treat an affine base. There a
quasi-compact fpqc covering is refined by a finite family of affine schemes flat over the base;
their coproduct is affine, flat and surjective over the base, hence faithfully flat on global
sections, and finite presentation of modules descends along a faithfully flat ring map.
Assembling the affine pieces uses that a module with a finite global presentation on each member
of an open cover is of finite presentation.

## References

* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u v

open CategoryTheory
open CategoryTheory.Limits
open Stacks.AlgebraicGeometry.FlatBaseChange
open scoped TensorProduct

/-- Finite presentation of the pullback along `f` passes to the pullback along `g ≫ f`. -/
private theorem isFinitePresentation_pullback_comp
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules)
    (h : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation) :
    ((Scheme.Modules.pullback (g ≫ f)).obj M).IsFinitePresentation :=
  have := h
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackComp g f).app M)
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback g _)

/-- Finite presentation of the pullbacks along a covering passes to the pullbacks along a
refinement of it. -/
private theorem isFinitePresentation_on_affine_refinement
    {S : Scheme.{u}} (M : S.Modules)
    (𝒰 : S.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj M).IsFinitePresentation)
    (𝒱 : Scheme.AffineCover.{v} @Flat S) (f : 𝒱.cover ⟶ 𝒰.forgetQc)
    (j : 𝒱.I₀) :
    ((Scheme.Modules.pullback (𝒱.f j)).obj M).IsFinitePresentation := by
  show ((Scheme.Modules.pullback (𝒱.cover.f j)).obj M).IsFinitePresentation
  rw [← f.w₀ j]
  exact isFinitePresentation_pullback_comp _ _ M (h _)

/-- The associated sheaf of a module is finitely presented as soon as its pullback along a
faithfully flat map of affine schemes is. -/
@[ega "IV 2.5.3" "partial", sga "4½ Arcata 1.4.2"]
private theorem tilde_isFinitePresentation_of_faithfullyFlat_baseChange
    {R S : CommRingCat.{u}} [Algebra R S] [Module.FaithfullyFlat R S]
    (M : ModuleCat.{u} R)
    (h : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)).IsFinitePresentation) :
    (tilde M).IsFinitePresentation := by
  apply (AlgebraicGeometry.tilde_isFinitePresentation_iff M).2
  have hS : (tilde ((ModuleCat.extendScalars (algebraMap R S)).obj M)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec S).ringCatSheaf).prop_of_iso
      ((pullbackTildeIso R S
        (CommRingCat.ofHom (algebraMap R S))).app M) h
  have hM : Module.FinitePresentation S ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    (AlgebraicGeometry.tilde_isFinitePresentation_iff _).1 hS
  let T := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : T ≃ₗ[S] S :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have htensor : Module.FinitePresentation S (S ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)).finitePresentation_iff.mp hM
  exact Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat
    (TensorProduct.mk R S M 1) (TensorProduct.isBaseChange R M S)

/-- Finite presentation of a quasi-coherent module on an affine scheme descends along a flat
surjective morphism of affine schemes. -/
@[ega "IV 2.5.2" "(ii), special case", sga "1 VIII 1.10" "special case"]
private theorem isFinitePresentation_of_affine_flat_surjective
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] [Surjective f]
    (M : Y.Modules) [M.IsQuasicoherent]
    (h : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let φ : R ⟶ S := f.appTop
  let : Algebra R S := φ.hom.toAlgebra
  let : Module.FaithfullyFlat R S :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹Flat f›, ‹Surjective f›⟩
  let N : (Spec R).Modules := (Scheme.Modules.pullback Y.isoSpec.inv).obj M
  let : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      Y.isoSpec.inv M
  have hY : ((Scheme.Modules.pullback (X.isoSpec.inv ≫ f)).obj M).IsFinitePresentation :=
    isFinitePresentation_pullback_comp _ _ M h
  have hN : ((Scheme.Modules.pullback (Spec.map φ)).obj N).IsFinitePresentation := by
    have hY' : ((Scheme.Modules.pullback (Spec.map φ ≫ Y.isoSpec.inv)).obj
        M).IsFinitePresentation := by
      show ((Scheme.Modules.pullback (Spec.map f.appTop ≫ Y.isoSpec.inv)).obj
        M).IsFinitePresentation
      rw [Scheme.isoSpec_inv_naturality f]
      exact hY
    exact (SheafOfModules.isFinitePresentation (Spec S).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp (Spec.map φ) Y.isoSpec.inv).app M).symm hY'
  let A : ModuleCat R := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let e : tilde A ≅ N := asIso N.fromTildeΓ
  have hA : ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde A)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec S).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso e).symm hN
  have htilde : (tilde A).IsFinitePresentation :=
    tilde_isFinitePresentation_of_faithfullyFlat_baseChange A hA
  have hN' : N.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e htilde
  have hM : ((Scheme.Modules.pullback Y.isoSpec.hom).obj N).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback Y.isoSpec.hom N
  let eM : ((Scheme.Modules.pullback Y.isoSpec.hom).obj N) ≅ M :=
    ((Scheme.Modules.pullbackComp Y.isoSpec.hom Y.isoSpec.inv).app M) ≪≫
      ((Scheme.Modules.pullbackCongr (by simp : Y.isoSpec.hom ≫ Y.isoSpec.inv = 𝟙 Y)).app M) ≪≫
      ((Scheme.Modules.pullbackId Y).app M)
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso eM hM

/-- A finite global presentation of the restriction of a module to an open transports to the
localization of the module at that open. -/
theorem over_has_finite_global_presentation
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    ∃ Q : (M.over U).Presentation, Q.IsFinite := by
  let e := Scheme.Modules.overEquiv U
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} e.inverse :=
    CategoryTheory.Adjunction.isEquivalence_preservesColimits e.inverse
  have hpres : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      e.inverse := inferInstance
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      e.inverse.obj (SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
    (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm
  let P' : (e.inverse.obj (M.restrict U.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P e.inverse hpres η
  let iso : e.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm) ≪≫
      (e.unitIso.app (M.over U)).symm
  have : P'.IsFinite :=
    ⟨⟨‹P.IsFinite›.isFiniteType_generators.finite⟩, ⟨‹P.IsFinite›.isFiniteType_relations.finite⟩⟩
  exact ⟨P'.ofIsIso iso.hom, inferInstance⟩

/-- A module whose restriction to an open admits a finite global presentation is finitely
presented on the localization at that open. -/
theorem over_isFinitePresentation_of_finite_global
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (M.over U).IsFinitePresentation := by
  obtain ⟨Q, hQ⟩ := over_has_finite_global_presentation U M P
  let q := Q.quasicoherentData
  refine { exists_quasicoherentData := ⟨q.shrink, ?_⟩ }
  exact { isFinite_presentation := fun _ =>
    ⟨⟨hQ.isFiniteType_generators.finite⟩, ⟨hQ.isFiniteType_relations.finite⟩⟩ }

/-- A finitely presented quasi-coherent module on an affine scheme admits a finite global
presentation. -/
private theorem affine_has_finite_global_presentation
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFinitePresentation] :
    ∃ P : M.Presentation, P.IsFinite := by
  let R := Γ(X, ⊤)
  let N : (Spec R).Modules := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  let : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      X.isoSpec.inv M
  let : N.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback X.isoSpec.inv M
  let A : ModuleCat R := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let e : tilde A ≅ N := asIso N.fromTildeΓ
  have htilde : (tilde A).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e.symm
      (inferInstance : N.IsFinitePresentation)
  let : Module.FinitePresentation R A :=
    (AlgebraicGeometry.tilde_isFinitePresentation_iff A).mp htilde
  obtain ⟨P, hP⟩ := tilde_has_finite_presentation A
  let : P.IsFinite := hP
  let P' := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom P
  let : P'.IsFinite :=
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  let P'' := Scheme.Modules.presentationRestrict X.isoSpec.hom P'
  have : P''.IsFinite :=
    ⟨⟨‹P'.IsFinite›.isFiniteType_generators.finite⟩, ⟨‹P'.IsFinite›.isFiniteType_relations.finite⟩⟩
  let eN : N.restrict X.isoSpec.hom ≅ M :=
    ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app N) ≪≫
      ((Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app M) ≪≫
      ((Scheme.Modules.pullbackCongr
        (by simp : X.isoSpec.hom ≫ X.isoSpec.inv = 𝟙 X)).app M) ≪≫
      ((Scheme.Modules.pullbackId X).app M)
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    eN.hom eN.isIso_hom P''
  exact ⟨Q, ⟨‹P''.IsFinite›.isFiniteType_generators.finite⟩,
    ⟨‹P''.IsFinite›.isFiniteType_relations.finite⟩⟩

/-- A sheaf of modules on a site is finitely presented as soon as it is finitely presented on the
localizations at the members of a covering of the final object. -/
lemma isFinitePresentation_of_coversTop
    {C : Type u} [CategoryTheory.Category.{u} C]
    {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{u}}
    [CategoryTheory.Limits.HasBinaryProducts C]
    [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, CategoryTheory.HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type u} (X : I → C)
    (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFinitePresentation] :
    M.IsFinitePresentation := by
  let D (i : I) := (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (M.over (X i))).choose
  let (i : I) : (D i).IsFinitePresentation :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (X i))).choose_spec
  let q := SheafOfModules.QuasicoherentData.bind M X hX D
  refine ⟨q, ?_⟩
  constructor
  intro i
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  all_goals constructor
  · exact inferInstanceAs (Finite ((D i.1).presentation i.2).generators.I)
  · exact inferInstanceAs (Finite ((D i.1).presentation i.2).relations.I)

/-- The previous criterion for a covering family indexed by an arbitrary small type. -/
private lemma isFinitePresentation_of_coversTop_small
    {C : Type u} [CategoryTheory.Category.{u} C]
    {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{u}}
    [CategoryTheory.Limits.HasBinaryProducts C]
    [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, CategoryTheory.HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type v} [Small.{u} I] (X : I → C)
    (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFinitePresentation] :
    M.IsFinitePresentation := by
  let e := equivShrink I
  let X' : Shrink.{u} I → C := fun j ↦ X (e.symm j)
  have hX' : J.CoversTop X' := by
    intro Y
    apply J.superset_covering ?_ (hX Y)
    intro Z f hf
    obtain ⟨i, ⟨g⟩⟩ := hf
    refine ⟨e i, ⟨?_⟩⟩
    simpa only [X', e.symm_apply_apply] using g
  let (j : Shrink.{u} I) : (M.over (X' j)).IsFinitePresentation :=
    inferInstanceAs ((M.over (X (e.symm j))).IsFinitePresentation)
  exact isFinitePresentation_of_coversTop M X' hX'

/-- Finite presentation of a module on a scheme is local on an affine open cover. -/
private theorem isFinitePresentation_of_affineOpenCover
    {X : Scheme.{u}} (M : X.Modules)
    (𝒲 : X.OpenCover.{v}) [Small.{u} 𝒲.I₀] [∀ i, IsAffine (𝒲.X i)]
    (h : ∀ i, ((Scheme.Modules.pullback (𝒲.f i)).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let U (i : 𝒲.I₀) : X.Opens := (𝒲.f i).opensRange
  have hU : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact 𝒲.isOpenCover_opensRange
  have (i : 𝒲.I₀) : (M.over (U i)).IsFinitePresentation := by
    let f := 𝒲.f i
    have hcomp := isFinitePresentation_pullback_comp f.isoOpensRange.inv f M (h i)
    have hrestr : ((Scheme.Modules.pullback (U i).ι).obj M).IsFinitePresentation := by
      rwa [f.isoOpensRange_inv_comp] at hcomp
    have hr : (M.restrict (U i).ι).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (U i : Scheme).ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M).symm hrestr
    let : IsAffine (U i : Scheme) := isAffineOpen_opensRange f
    let : SheafOfModules.IsQuasicoherent.{u, u, u} (M.restrict (U i).ι) := by
      obtain ⟨q, _⟩ := hr.exists_quasicoherentData
      exact ⟨⟨q.shrink⟩⟩
    obtain ⟨P, hP⟩ := affine_has_finite_global_presentation (M.restrict (U i).ι)
    let : P.IsFinite := hP
    exact over_isFinitePresentation_of_finite_global (U i) M P
  exact isFinitePresentation_of_coversTop_small M U hU

/-- Finite presentation of a quasi-coherent module on an affine scheme descends along an fpqc
covering. -/
@[ega "IV 2.5.2" "(ii), special case", sga "1 VIII 1.10" "special case"]
private theorem isFinitePresentation_of_fpqcCover_affine
    {S : Scheme.{u}} [IsAffine S] (M : S.Modules) [M.IsQuasicoherent]
    (𝒰 : S.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  obtain ⟨𝒱, f, hfinite, _⟩ := exists_finite_affine_refinement 𝒰
  let : Finite 𝒱.cover.I₀ := hfinite
  let : Small.{u} 𝒱.cover.I₀ := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒱.cover.I₀
    exact Small.mk' (e.trans (Equiv.ulift.{u} (α := Fin n)).symm)
  have (i : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X i) := inferInstanceAs (IsAffine (Spec (𝒱.X i)))
  let g := CategoryTheory.Limits.Sigma.desc 𝒱.cover.f
  let T := ∐ 𝒱.cover.X
  let N : T.Modules := (Scheme.Modules.pullback g).obj M
  let 𝒲 := sigmaOpenCover 𝒱.cover.X
  let : Finite 𝒲.I₀ := inferInstanceAs (Finite 𝒱.cover.I₀)
  let : Small.{u} 𝒲.I₀ := inferInstanceAs (Small.{u} 𝒱.cover.I₀)
  have (i : 𝒲.I₀) : IsAffine (𝒲.X i) := inferInstanceAs (IsAffine (Spec (𝒱.X i)))
  have hN : N.IsFinitePresentation := by
    refine isFinitePresentation_of_affineOpenCover N 𝒲 fun i => ?_
    have hcomp : ((Scheme.Modules.pullback (𝒱.cover.f i)).obj M).IsFinitePresentation :=
      isFinitePresentation_on_affine_refinement M 𝒰 h 𝒱 f i
    rw [← CategoryTheory.Limits.Sigma.ι_desc 𝒱.cover.f i] at hcomp
    exact (SheafOfModules.isFinitePresentation (𝒲.X i).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp (𝒲.f i) g).app M).symm hcomp
  obtain ⟨hflat, hsurj, _⟩ := affine_sigmaDesc_fpqc 𝒱
  let : Flat g := hflat
  let : Surjective g := hsurj
  exact isFinitePresentation_of_affine_flat_surjective g M hN

/-- A quasi-coherent module whose pullback to every member of an fpqc covering is finitely
presented is itself finitely presented. -/
@[stacks 05B0, sga "1 VIII 1.10" "finite presentation"]
public theorem isFinitePresentation_of_pullback_fpqcCover
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (𝒰 : X.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let 𝒲 := X.affineOpenCover.openCover
  have (i : 𝒲.I₀) : IsAffine (𝒲.X i) := inferInstanceAs (IsAffine (Spec (X.affineOpenCover.X i)))
  refine isFinitePresentation_of_affineOpenCover M 𝒲 fun i => ?_
  let N : (𝒲.X i).Modules := (Scheme.Modules.pullback (𝒲.f i)).obj M
  let 𝒱 := 𝒰.pullback₁ (𝒲.f i)
  have h𝒱 : ∀ j, ((Scheme.Modules.pullback (𝒱.f j)).obj N).IsFinitePresentation := by
    intro j
    let q : 𝒱.X j ⟶ 𝒰.X j := pullback.snd (𝒲.f i) (𝒰.f j)
    have hcomp := isFinitePresentation_pullback_comp q (𝒰.f j) M (h j)
    have hcomp' : ((Scheme.Modules.pullback (𝒱.f j ≫ 𝒲.f i)).obj M).IsFinitePresentation := by
      rwa [← show q ≫ 𝒰.f j = 𝒱.f j ≫ 𝒲.f i from pullback.condition.symm]
    exact (SheafOfModules.isFinitePresentation (𝒱.X j).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp (𝒱.f j) (𝒲.f i)).app M).symm hcomp'
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (𝒲.X i).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (𝒲.f i)).app M)
      (by infer_instance : (M.restrict (𝒲.f i)).IsQuasicoherent)
  exact isFinitePresentation_of_fpqcCover_affine N 𝒱 h𝒱

end AlgebraicGeometry

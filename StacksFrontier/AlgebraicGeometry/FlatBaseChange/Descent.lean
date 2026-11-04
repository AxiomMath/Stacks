module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Finiteness.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Finite type descends along fpqc coverings

[Stacks, Tag 05AZ]: a quasi-coherent `𝒪_X`-module is of finite type as soon as its pullback to
every member of an fpqc covering is. This file proves it,
`Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`.

The statement is local on the base, so it suffices to treat an affine base. There a
quasi-compact fpqc covering is refined by a finite family of affine schemes flat over the base;
their coproduct is affine, flat and surjective over the base, hence faithfully flat on global
functions; and finite generation of modules descends along a faithfully flat ring map, which is
[Stacks, Tag 03C4] and is Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`:
  **[Stacks, Tag 05AZ].** Finite type of a quasi-coherent module descends along an fpqc
  covering.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_specMap_pullback`: the affine core,
  read on a faithfully flat ring map and the associated sheaf of a module.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_flat_surjective_of_isAffine`: the
  affine case, for a flat surjective morphism of affine schemes.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_openCover`: being of finite type is
  local on an open cover of a scheme.

## Implementation notes

The shape of the argument is that of
`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`
(`StacksFrontier/AlgebraicGeometry/Descent/Modules/FpqcFinitePresentation.lean`, [Stacks, Tag
05B0]), whose affine pieces are reused here in the finite-type form. The one ingredient the
finite-presentation file does not have an analogue of is the transport of
`SheafOfModules.IsFiniteType` from `M.restrict U.ι` to `M.over U` for an open `U` of a scheme;
it is `isFiniteType_over` here, proved from the generic site statement
`isFiniteType_pushforward` along the equivalence between the slice of the opens site at `U` and
the opens site of `U`. With that, locality is `Stacks.SheafOfModules.LocalKernel`'s
`isFiniteType_of_coversTop` and no finite global generating family is needed, which is why the
finite-presentation file's affine presentation machinery has no counterpart below.

Several invertibility and finite-type hypotheses are passed as *explicit* arguments rather than
as instances (`isFiniteType_pushforward` takes `hφ` and `hM` explicitly, and each use of
`Stacks.SheafOfModules.isFiniteType_of_iso` is preceded by a `have` that restates its source in
the spelling the iso uses). The reason is that instance search compares the objects at
`instances` transparency, where `(F ⋙ G).obj M` and `G.obj (F.obj M)` do not agree; an explicit
argument is checked at default transparency instead.

## References

* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### The affine core -/

/-- The pullback of a module of finite type along a morphism of schemes is of finite type —
[Stacks, Tag 01B6] read for schemes. -/
theorem isFiniteType_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFiniteType] : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
  AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M

/-- If `f^* M` is of finite type, then so is `(g ≫ f)^* M`. -/
private theorem isFiniteType_pullback_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (M : X.Modules) (h : ((Scheme.Modules.pullback f).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback (g ≫ f)).obj M).IsFiniteType :=
  have _ : ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).obj M).IsFiniteType :=
    have _ := h
    isFiniteType_pullback g _
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.pullbackComp g f).app M)

/-- If `(g ≫ f)^* M` is of finite type, then so is `g^* (f^* M)`. -/
private theorem isFiniteType_pullback_pullback_of_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (f : Y ⟶ X) (M : X.Modules) (h : ((Scheme.Modules.pullback (g ≫ f)).obj M).IsFiniteType) :
    ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)).IsFiniteType :=
  have _ := h
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.pullbackComp g f).app M).symm

/-- **[Stacks, Tag 03C4] for the associated sheaf of a module.** If the pullback of `M^~` along
`Spec S ⟶ Spec R` is of finite type and `S` is faithfully flat over `R`, then `M^~` is of finite
type; equivalently, `M` is a finite `R`-module as soon as `S ⊗[R] M` is a finite `S`-module.

This is `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` read through
`AlgebraicGeometry.tilde_isFiniteType_iff` and `AlgebraicGeometry.pullbackTildeIso`. -/
theorem isFiniteType_of_specMap_pullback {R S : CommRingCat.{u}} [Algebra R S]
    [Module.FaithfullyFlat R S] (M : ModuleCat.{u} R)
    (h : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde M)).IsFiniteType) :
    (tilde M).IsFiniteType := by
  refine (AlgebraicGeometry.tilde_isFiniteType_iff M).2 ?_
  have h' : ((tilde.functor R ⋙
      Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M).IsFiniteType := h
  have hS : (tilde ((ModuleCat.extendScalars (algebraMap R S)).obj M)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((pullbackTildeIso R S (CommRingCat.ofHom (algebraMap R S))).app M)
  have hM : Module.Finite S ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    (AlgebraicGeometry.tilde_isFiniteType_iff _).1 hS
  let T := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : T ≃ₗ[S] S :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have htensor : Module.Finite S (S ⊗[R] M) :=
    (Module.Finite.equiv_iff
      (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M))).mp hM
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (T := S) (M := M)

/-- **The affine case of [Stacks, Tag 05AZ].** Let `f : X ⟶ Y` be a flat surjective morphism of
affine schemes and let `M` be a quasi-coherent `𝒪_Y`-module. If `f^* M` is of finite type, then
so is `M`. -/
theorem isFiniteType_of_flat_surjective_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] [Surjective f] (M : Y.Modules) [M.IsQuasicoherent]
    (h : ((Scheme.Modules.pullback f).obj M).IsFiniteType) : M.IsFiniteType := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let φ : R ⟶ S := f.appTop
  let _ : Algebra R S := φ.hom.toAlgebra
  let _ : Module.FaithfullyFlat R S :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹Flat f›, ‹Surjective f›⟩
  let N : (Spec R).Modules := (Scheme.Modules.pullback Y.isoSpec.inv).obj M
  let _ : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      Y.isoSpec.inv M
  have hY : ((Scheme.Modules.pullback (X.isoSpec.inv ≫ f)).obj M).IsFiniteType :=
    isFiniteType_pullback_comp X.isoSpec.inv f M h
  have hN : ((Scheme.Modules.pullback (Spec.map φ)).obj N).IsFiniteType := by
    have hY' : ((Scheme.Modules.pullback (Spec.map φ ≫ Y.isoSpec.inv)).obj M).IsFiniteType := by
      show ((Scheme.Modules.pullback (Spec.map f.appTop ≫ Y.isoSpec.inv)).obj M).IsFiniteType
      rw [Scheme.isoSpec_inv_naturality f]
      exact hY
    exact isFiniteType_pullback_pullback_of_comp (Spec.map φ) Y.isoSpec.inv M hY'
  let A : ModuleCat R := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let e : tilde A ≅ N := asIso N.fromTildeΓ
  have hA : ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde A)).IsFiniteType :=
    have _ := hN
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso e).symm
  have htilde : (tilde A).IsFiniteType := isFiniteType_of_specMap_pullback A hA
  have hN' : N.IsFiniteType :=
    have _ := htilde
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e
  have hM : ((Scheme.Modules.pullback Y.isoSpec.hom).obj N).IsFiniteType :=
    have _ := hN'
    isFiniteType_pullback Y.isoSpec.hom N
  let eM : (Scheme.Modules.pullback Y.isoSpec.hom).obj N ≅ M :=
    (Scheme.Modules.pullbackComp Y.isoSpec.hom Y.isoSpec.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr (by simp : Y.isoSpec.hom ≫ Y.isoSpec.inv = 𝟙 Y)).app M ≪≫
      (Scheme.Modules.pullbackId Y).app M
  have _ := hM
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} eM

/-! ### Locality on an open cover -/

/-- **Finite type is preserved by a pushforward of sheaves of modules along a continuous and
cocontinuous functor of sites** whose structure-sheaf comparison `φ` is invertible: a family of
local generators is carried to the family indexed by the objects of the source site lying over
the members of the given one. -/
theorem isFiniteType_pushforward
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    [G.IsLeftAdjoint] (hφ : IsIso φ)
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    (M : SheafOfModules.{u} R) (hM : M.IsFiniteType) :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  have := hφ
  have := hM
  obtain ⟨P, hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let Q : ((SheafOfModules.pushforward φ).obj M).LocalGeneratorsData := {
    I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
    X i := i.1
    coversTop Y := by
      refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
      intro Z g ⟨i, ⟨v⟩⟩
      exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
    generators i := by
      let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
      have : G'.IsContinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        Functor.isContinuous_comp _ _ _ (J.over _) _
      have : G'.IsCocontinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        isCocontinuous_comp _ _ _ (J.over _)
      let ψ : S.over i.1 ⟶ (G'.sheafPushforwardContinuous RingCat.{u}
          (K.over i.1) (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
        ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
      have hψ : IsIso ψ :=
        Functor.map_isIso
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K) φ
      have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
        SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
      let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
        SheafOfModules.pushforward (𝟙 _)
      let e : (SheafOfModules.pushforward ψ).obj (SheafOfModules.unit (R.over (P.X i.2.1))) ≅
          SheafOfModules.unit (S.over i.1) := overS.mapIso η
      exact (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm }
  refine SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨Q, ?_⟩
  constructor
  intro i
  constructor
  exact (hP.isFiniteType i.2.1).finite

/-- An equivalence of sites induces a continuous functor on every slice. -/
alias overPost_isContinuous_of_equivalence :=
  Stacks.AlgebraicGeometry.CoherentTFAE.isContinuous_overPost_of_isEquivalence

/-- If the restriction of `M` to an open subscheme `U` is of finite type, then so is the
localization `M.over U`. -/
theorem isFiniteType_over {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (hM : (M.restrict U.ι).IsFiniteType) : (M.over U).IsFiniteType := by
  have := hM
  have := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_overEquiv_inverse U
    (M.restrict U.ι)
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.overEquiv U).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U)).symm)

/-- Being of finite type is local on the base, for a covering family of the final open indexed
by a small type. -/
theorem isFiniteType_of_coversTop_small {X : Scheme.{u}} (M : X.Modules) {I : Type v}
    [Small.{u} I] (U : I → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (h : ∀ i, (M.over (U i)).IsFiniteType) : M.IsFiniteType := by
  let e := equivShrink I
  let U' : Shrink.{u} I → X.Opens := fun j => U (e.symm j)
  have hU' : (Opens.grothendieckTopology X).CoversTop U' := by
    intro Y
    refine (Opens.grothendieckTopology X).superset_covering ?_ (hU Y)
    intro Z g hg
    obtain ⟨i, ⟨g'⟩⟩ := hg
    exact ⟨e i, ⟨by simpa only [U', e.symm_apply_apply] using g'⟩⟩
  exact Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop M U' hU'
    fun j => h (e.symm j)

/-- **Being of finite type is local on an open cover of a scheme.** -/
theorem isFiniteType_of_openCover {X : Scheme.{u}} (M : X.Modules) (𝒲 : X.OpenCover.{v})
    [Small.{u} 𝒲.I₀]
    (h : ∀ i, ((Scheme.Modules.pullback (𝒲.f i)).obj M).IsFiniteType) : M.IsFiniteType := by
  let U (i : 𝒲.I₀) : X.Opens := (𝒲.f i).opensRange
  have hU : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff (X : Type u) U).2 𝒲.isOpenCover_opensRange
  refine isFiniteType_of_coversTop_small M U hU fun i => ?_
  have hcomp := isFiniteType_pullback_comp (𝒲.f i).isoOpensRange.inv (𝒲.f i) M (h i)
  rw [(𝒲.f i).isoOpensRange_inv_comp] at hcomp
  have hr : (M.restrict (U i).ι).IsFiniteType :=
    have _ := hcomp
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M).symm
  exact isFiniteType_over (U i) M hr

/-! ### Descent along an fpqc covering -/

/-- A quasi-compact fpqc covering of an affine scheme is refined, through open immersions, by a
finite affine covering by flat morphisms. -/
theorem exists_finite_affine_refinement
    {S : Scheme.{u}} [IsAffine S] (𝒰 : S.Cover.{v} Scheme.fpqcPrecoverage) :
    ∃ (𝒱 : Scheme.AffineCover.{v} @Flat S) (f : 𝒱.cover ⟶ 𝒰.forgetQc),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  let _ : MorphismProperty.RespectsLeft (@Flat) (@IsOpenImmersion) :=
    (inferInstance : MorphismProperty.Respects (@Flat) (@IsOpenImmersion)).toRespectsLeft
  let _ : QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp (𝒰.mem₀ : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S).1
  have : CompactSpace S := inferInstance
  exact QuasiCompactCover.exists_hom (P := @Flat) (𝒰 := 𝒰.forgetQc)

/-- The map out of the coproduct of a finite affine flat covering of an affine scheme is flat,
surjective and quasi-compact. -/
theorem affine_sigmaDesc_fpqc {S : Scheme.{u}} [IsAffine S]
    (𝒱 : Scheme.AffineCover.{v} @Flat S) [Finite 𝒱.I₀] [Small.{u} 𝒱.cover.I₀] :
    Flat (Sigma.desc 𝒱.cover.f) ∧ Surjective (Sigma.desc 𝒱.cover.f) ∧
      QuasiCompact (Sigma.desc 𝒱.cover.f) := by
  let _ : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have (j : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X j) := inferInstanceAs (IsAffine (Spec (𝒱.X j)))
  have : IsAffine (∐ 𝒱.cover.X) := inferInstance
  have (j : 𝒱.cover.I₀) : Flat (𝒱.cover.f j) := 𝒱.map_prop j
  have : Surjective (Sigma.desc 𝒱.cover.f) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := 𝒱.covers x
    refine ⟨Sigma.ι 𝒱.cover.X (𝒱.idx x) y, ?_⟩
    calc (Sigma.desc 𝒱.cover.f) (Sigma.ι 𝒱.cover.X (𝒱.idx x) y)
        = (Sigma.ι 𝒱.cover.X (𝒱.idx x) ≫ Sigma.desc 𝒱.cover.f) y := rfl
      _ = (𝒱.cover.f (𝒱.idx x)) y :=
          congrArg (fun q : 𝒱.cover.X (𝒱.idx x) ⟶ S => q y)
            (Sigma.ι_desc 𝒱.cover.f (𝒱.idx x))
      _ = x := hy
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Finite type of a quasi-coherent module on an *affine* scheme descends along an fpqc
covering. -/
theorem isFiniteType_of_fpqcCover_affine {S : Scheme.{u}} [IsAffine S] (M : S.Modules)
    [M.IsQuasicoherent] (𝒰 : S.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj M).IsFiniteType) : M.IsFiniteType := by
  obtain ⟨𝒱, f, hfinite, _⟩ := exists_finite_affine_refinement 𝒰
  let _ : Finite 𝒱.I₀ := hfinite
  let _ : Finite 𝒱.cover.I₀ := hfinite
  let _ : Small.{u} 𝒱.cover.I₀ := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒱.cover.I₀
    exact Small.mk' (e.trans (Equiv.ulift.{u} (α := Fin n)).symm)
  have (i : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X i) := inferInstanceAs (IsAffine (Spec (𝒱.X i)))
  let g := Sigma.desc 𝒱.cover.f
  let N : (∐ 𝒱.cover.X).Modules := (Scheme.Modules.pullback g).obj M
  let 𝒲 := sigmaOpenCover 𝒱.cover.X
  let _ : Finite 𝒲.I₀ := inferInstanceAs (Finite 𝒱.cover.I₀)
  let _ : Small.{u} 𝒲.I₀ := inferInstanceAs (Small.{u} 𝒱.cover.I₀)
  have hN : N.IsFiniteType := by
    refine isFiniteType_of_openCover N 𝒲 fun i => ?_
    let j := f.s₀ i
    have hj : ((Scheme.Modules.pullback (𝒰.f j)).obj M).IsFiniteType := h j
    have hcomp := isFiniteType_pullback_comp (f.h₀ i) (𝒰.f j) M hj
    rw [f.w₀ i, ← Sigma.ι_desc 𝒱.cover.f i] at hcomp
    exact isFiniteType_pullback_pullback_of_comp (𝒲.f i) g M hcomp
  obtain ⟨hflat, hsurj, _⟩ := affine_sigmaDesc_fpqc 𝒱
  let _ : Flat g := hflat
  let _ : Surjective g := hsurj
  exact isFiniteType_of_flat_surjective_of_isAffine g M hN

/-- **Stacks Project, Tag 05AZ.** Let `X` be a scheme and `M` a quasi-coherent `𝒪_X`-module. If
`{f i : 𝒰.X i ⟶ X}` is an fpqc covering of `X` such that every pullback `(f i)^* M` is of finite
type, then `M` is of finite type. -/
@[stacks 05AZ]
theorem isFiniteType_of_pullback_fpqcCover {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (𝒰 : X.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj M).IsFiniteType) : M.IsFiniteType := by
  let 𝒲 := X.affineOpenCover.openCover
  have (i : 𝒲.I₀) : IsAffine (𝒲.X i) := inferInstanceAs (IsAffine (Spec (X.affineOpenCover.X i)))
  refine isFiniteType_of_openCover M 𝒲 fun i => ?_
  let N : (𝒲.X i).Modules := (Scheme.Modules.pullback (𝒲.f i)).obj M
  let 𝒱 := 𝒰.pullback₁ (𝒲.f i)
  have h𝒱 : ∀ j, ((Scheme.Modules.pullback (𝒱.f j)).obj N).IsFiniteType := by
    intro j
    let q : 𝒱.X j ⟶ 𝒰.X j := CategoryTheory.Limits.pullback.snd (𝒲.f i) (𝒰.f j)
    have hcomp := isFiniteType_pullback_comp q (𝒰.f j) M (h j)
    have heq : q ≫ 𝒰.f j = 𝒱.f j ≫ 𝒲.f i := CategoryTheory.Limits.pullback.condition.symm
    rw [heq] at hcomp
    exact isFiniteType_pullback_pullback_of_comp (𝒱.f j) (𝒲.f i) M hcomp
  have _ : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (𝒲.X i).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (𝒲.f i)).app M)
      (by infer_instance : (M.restrict (𝒲.f i)).IsQuasicoherent)
  exact isFiniteType_of_fpqcCover_affine N 𝒱 h𝒱

end Stacks.AlgebraicGeometry.FlatBaseChange

end

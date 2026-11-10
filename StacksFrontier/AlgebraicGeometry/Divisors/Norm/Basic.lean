module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Norm.Projective
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackLocallyFree
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections

/-!
# The norm of a finite locally free morphism

A *norm* for a morphism `f : X ⟶ Y` of schemes is a map `f_* 𝒪_X ⟶ 𝒪_Y` which is
multiplicative on sections, compatible with restriction, and sends a section vanishing at a
point of `X` to one vanishing at its image. It has *degree `d`* when the norm of a function
pulled back from `Y` is its `d`-th power.

A finite locally free morphism has a canonical such norm: on an affine open `U ⊆ Y` the algebra
`Γ(X, f⁻¹U)` is finite projective over `Γ(Y, U)`, and the norm is the determinant of
multiplication, `Algebra.projectiveNorm`. This needs no constant or positive rank; at constant
rank `d` it is a norm of degree `d`, which is Tag 0BD2.

## Main definitions

* `Stacks.Norm.MorphismNormMap` is a multiplicative sheaf map preserving pointwise
  vanishing.
* `Stacks.Norm.MorphismNorm` is a norm of a specified degree for a morphism of schemes.
* `Stacks.Norm.HasNormOfDegree` asserts the existence of such a norm.
* `Stacks.Norm.IsDeterminantNorm` characterizes a norm by the local determinant formula.
* `Stacks.Divisors.DeterminantNorm` bundles the determinant formula and the constant-rank power
  law.
* `Stacks.Divisors.finiteLocallyFreeNorm` is the canonical norm of a finite locally free
  morphism.
* `Stacks.Divisors.finiteLocallyFreeNormOfRank` specializes it to positive constant rank.

## Main results

* `Stacks.Divisors.finiteLocallyFreeNorm_app_affine_eq_projectiveNorm` identifies the canonical
  norm with `Algebra.projectiveNorm` on an affine open of the target.
* `Stacks.Divisors.finiteLocallyFreeNorm_app_baseChange` is compatibility of the canonical norm
  with an arbitrary cartesian base-change square, for a square both of whose vertical arrows
  are finite locally free.
* `Stacks.Divisors.finiteLocallyFreeNormOfRank_app_baseChange` is the positive constant-rank
  case.

## Implementation notes

The determinant construction works without a constant positive rank, as is also needed for
Tag 0BW8; its positive constant-rank specialization has the norm properties of Tag 0BD2.

On an affine open `U ⊆ Y` with `f⁻¹U` affine, `Γ(X, f⁻¹U)` is finite projective — not in
general free — over `Γ(Y, U)`, so the norm is `Algebra.projectiveNorm`, the scalar determinant
on the exterior determinant line, rather than `Algebra.norm`. The affine-open values are glued
to a map of sheaves of commutative monoids by `TopCat.Sheaf.restrictHomEquivHom` over the basis
of affine opens, which is why naturality is first proved between affine opens only.

Base-change compatibility is stated on sections pulled back around an arbitrary cartesian
square; the comparison uses `AlgebraicGeometry.Scheme.Hom.appLE` because the two inverse-image
opens are propositionally, rather than definitionally, equal. On affine opens the comparison is
Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`, which identifies
`Γ(X', f'⁻¹V)` with `Γ(Y', V) ⊗_{Γ(Y, U)} Γ(X, f⁻¹U)`.

The two base-change statements here assume that the base-changed morphism is itself finite
locally free. That hypothesis is the base-change stability of
`Stacks.Morphisms.IsFiniteLocallyFree`, which is the instance
`Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange` in
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange`; the full base-change
clause of Tag 0BD2 is `Stacks.Divisors.finiteLocallyFreeNorm_baseChange` in
`StacksFrontier.AlgebraicGeometry.NormBaseChange.Basic`.

## References

* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TensorProduct TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Divisors

open Stacks.Norm

/-- A family of opens covering the top sheaf-theoretically covers every point. -/
private lemma exists_mem_of_coversTop {X : Scheme.{u}} {ι : Type*} {U : ι → X.Opens}
    (hc : (Opens.grothendieckTopology X).CoversTop U) (x : X) : ∃ i, x ∈ U i := by
  rw [Opens.coversTop_iff] at hc
  have hx : x ∈ ⨆ i, U i := by rw [hc]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

/-- If `F` has a generating family over `U` that is an isomorphism with a free module, then
the restriction of `F` to `U` is free. -/
private lemma nonempty_restrict_iso_free {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (σ : (F.over U).GeneratingSections) [IsIso σ.π] :
    Nonempty (F.restrict (Scheme.Opens.ι U) ≅ SheafOfModules.free σ.I) :=
  ⟨((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (asIso σ.π).symm ≪≫
    (finiteFreeOverEquivIsoX X U σ.I).symm⟩

private lemma isFiniteLocallyFree_pointwise
    {X : Scheme.{u}} (F : X.Modules)
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    Scheme.Modules.IsFiniteLocallyFree F := by
  classical
  obtain ⟨q, hfree, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  intro x
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop q.coversTop x
  let : IsIso (q.generators i).π := hfree.isIso i
  obtain ⟨e⟩ := nonempty_restrict_iso_free F (q.X i) (q.generators i)
  let := hfinite.isFiniteType i
  exact ⟨q.X i, hi, (q.generators i).I, inferInstance, ⟨e⟩⟩

private lemma tilde_isFiniteLocallyFreeOfRank_of_sheaf
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (d : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R)
        (ModuleCat.of R (AlgebraicGeometry.moduleSpecΓFunctor.obj F))).IsFiniteLocallyFreeOfRank
      d := by
  classical
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  have hfrom : IsIso (F.fromTildeΓ) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) F
  let e : AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hfrom
  intro x
  obtain ⟨q, hfree, hrank⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hi⟩ := exists_mem_of_coversTop q.coversTop x
  let U := q.X i
  let : IsIso (q.generators i).π := hfree.isIso i
  obtain ⟨eLocal⟩ := nonempty_restrict_iso_free F U (q.generators i)
  let eTildeLocal := (Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e
  let eIndex : (q.generators i).I ≃ ULift (Fin d) :=
    (hrank i).some.trans Equiv.ulift.symm
  let eIndexFree :=
    (SheafOfModules.freeFunctor (R := (Scheme.Opens.toScheme U).ringCatSheaf)).mapIso
      eIndex.toIso
  exact ⟨U, hi, ⟨eTildeLocal ≪≫ eLocal ≪≫ eIndexFree⟩⟩

private lemma moduleSpecΓ_isFiniteLocallyFreeOfRank
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (d : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    Module.IsFiniteLocallyFreeOfRank R (AlgebraicGeometry.moduleSpecΓFunctor.obj F) d := by
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  exact (tilde_isFiniteLocallyFreeOfRank_iff R M d).mp
    (tilde_isFiniteLocallyFreeOfRank_of_sheaf F d hF)

private lemma moduleSpecΓ_rankAtStalk
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (d : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (AlgebraicGeometry.moduleSpecΓFunctor.obj F) p = d :=
  Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank d
    (moduleSpecΓ_isFiniteLocallyFreeOfRank F d hF)

private alias opens_map_final := Stacks.Topology.final_opensMap

private lemma isFiniteLocallyFreeOfRank_of_iso {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (r : ℕ) [hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r := by
  obtain ⟨q, hq, hrank⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u} N := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  have hq' : q'.IsLocallyFreeData.{u, u, u, u} := by
    refine ⟨fun i ↦ ?_⟩
    have h0 : IsIso (q.generators i).π := hq.isIso i
    have h2 : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom)) h2
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q', hq', hrank⟩ }

/-- Over an open `U` of the target, the pullback of sheaves of modules along `f` is computed by
a colimit-preserving functor on the over-sites that matches the global pullback, and that sends
the unit module to the unit module.

This is the local ingredient of `local_generators_pullback`: it is what lets a set of local
generators of `M` over `U` be carried to one of the pullback of `M` over `f⁻¹U`. -/
private lemma exists_overPullbackFunctor {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (U : Opens Y) :
    ∃ (G : SheafOfModules.{u} (S.over U) ⥤
        SheafOfModules.{u} (R.over ((Opens.map f).obj U)))
      (_ : PreservesColimitsOfSize.{u, u} G),
      Nonempty (SheafOfModules.unit (R.over ((Opens.map f).obj U)) ≅
        G.obj (SheafOfModules.unit (S.over U))) ∧
      Nonempty (G.obj (M.over U) ≅
        ((SheafOfModules.pullback φ).obj M).over ((Opens.map f).obj U)) := by
  let F := Opens.map f
  let ψ : S.obj ⟶ (Opens.map f).op ⋙ R.obj := φ.hom
  let : F.Final := opens_map_final f
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  let : F.PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opens_map f)
  let φU : S.over U ⟶
      ((Over.post F).sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology Y).over U)
        ((Opens.grothendieckTopology X).over (F.obj U))).obj (R.over (F.obj U)) :=
    ((Over.forget U).sheafPushforwardContinuous RingCat _ _).map φ
  let : (Over.post F : Over U ⥤ Over (F.obj U)).Final :=
    Stacks.AlgebraicGeometry.ComponentDegrees.opensOverPost_final f U
  have hprod : ∀ V : Opens ↑Y, IsIso (prodComparison F U V) := fun V ↦ inferInstance
  let e : Over.star U ⋙ Over.post F ≅ F ⋙ Over.star (F.obj U) :=
    NatIso.ofComponents (fun V ↦ Over.isoMk (@asIso _ _ _ _ _ (hprod V)))
  let : (Over.star U ⋙ Over.post F).IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over (F.obj U)) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology Y).over U) _
  let : (F ⋙ Over.star (F.obj U)).IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over (F.obj U)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  let eR :
      SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) (F.obj U)) ⋙
        SheafOfModules.pushforward φ ≅
      SheafOfModules.pushforward φU ⋙
        SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) U) :=
    SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardCongr₂ _ e (by
        ext : 2
        funext V
        change ψ.app V ≫ R.obj.map prod.snd.op ≫
            R.obj.map (prodComparison F U V.unop).op =
              S.obj.map prod.snd.op ≫ ψ.app _
        rw [← R.obj.map_comp, ← op_comp, prodComparison_snd]
        exact (ψ.naturality prod.snd.op).symm) ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
  let eL := ((conjugateIsoEquiv
    ((SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U)))
    ((SheafOfModules.overPushforwardOverAdj (R := S) U).comp
      (SheafOfModules.pullbackPushforwardAdjunction φU))).symm eR)
  refine ⟨SheafOfModules.pullback φU, inferInstance, ⟨?_, ⟨eL.app M⟩⟩⟩
  exact ⟨(asIso (SheafOfModules.pullbackObjUnitToUnit φU)).symm⟩

/-- Transporting generating sections along a colimit-preserving functor and then along an
isomorphism keeps the presentation an isomorphism. -/
private lemma isIso_map_ofEpi_π
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections) [IsIso σ.π]
    (G : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} G]
    (η : SheafOfModules.unit S ≅ G.obj (SheafOfModules.unit R))
    {N : SheafOfModules.{u} S} (ε : G.obj M ≅ N) :
    IsIso ((σ.map G η).ofEpi ε.hom).π := by
  have hx : IsIso (σ.map G η).π := inferInstance
  have hy : IsIso ((σ.map G η).π ≫ ε.hom) := @IsIso.comp_isIso _ _ _ _ _ _ _ hx inferInstance
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact hy

/-- Local generators of `M` pull back to local generators of the pullback of `M`, with the same
index type and the same local index types, over the preimages of the same opens. -/
theorem local_generators_pullback {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (q : SheafOfModules.LocalGeneratorsData.{u} M)
    (hq : q.IsLocallyFreeData) :
    ∃ q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u}
        ((SheafOfModules.pullback φ).obj M),
      q'.IsLocallyFreeData.{u, u, u, u} ∧ ∃ e : q'.I ≃ q.I,
        (∀ i, q'.X i = (Opens.map f).obj (q.X (e i))) ∧
        (∀ i, (q'.generators i).I = (q.generators (e i)).I) := by
  choose G hG eUnit eM using fun i ↦ exists_overPullbackFunctor f φ M (q.X i)
  let q' : ((SheafOfModules.pullback φ).obj M).LocalGeneratorsData := {
    I := q.I
    X i := (Opens.map f).obj (q.X i)
    coversTop := (Opens.coversTop_iff _ _).2
      (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
    generators i := ((q.generators i).map (G i) (eUnit i).some).ofEpi (eM i).some.hom }
  refine ⟨q', ?_, ⟨Equiv.refl _, ?_, ?_⟩⟩
  · constructor
    intro i
    have h0 : IsIso (q.generators i).π := hq.isIso i
    have h1 : PreservesColimitsOfSize.{u, u} (G i) := hG i
    exact isIso_map_ofEpi_π (q.generators i) (G i) (eUnit i).some (eM i).some
  · intro i
    rfl
  · intro i
    rfl

private lemma pullback_isFiniteLocallyFree
    {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.pullback g).obj M) := by
  obtain ⟨q, hq, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  obtain ⟨q', hq', e, _, hI⟩ :=
    local_generators_pullback g.base g.toRingCatSheafHom M q hq
  refine ⟨⟨q', hq', ⟨fun i ↦ ?_⟩⟩⟩
  have hsource : Finite ((q.generators (e i)).I) :=
    (hfinite.isFiniteType (e i)).finite
  exact ⟨Finite.of_equiv _ (Equiv.cast (hI i).symm)⟩

private lemma finiteProjective_sections_affineOpen
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (hF : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) ∧
      Module.Projective Γ(X, U.1) Γ(F, U.1) := by
  let f := U.2.fromSpec
  let : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app F
  have hPull : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj F) := pullback_isFiniteLocallyFree f F hF
  have hGsheaf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} G :=
    SheafOfModules.IsFiniteLocallyFree.of_iso e.symm (h := hPull)
  have hG : Scheme.Modules.IsFiniteLocallyFree G :=
    isFiniteLocallyFree_pointwise G hGsheaf
  let : G.IsQuasicoherent := inferInstance
  let : Module.Finite Γ(X, U.1) (AlgebraicGeometry.moduleSpecΓFunctor.obj G) :=
    (moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree G hG).1
  let : Module.Projective Γ(X, U.1) (AlgebraicGeometry.moduleSpecΓFunctor.obj G) :=
    (moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree G hG).2
  let : Module.Finite Γ(X, U.1) Γ(G, ⊤) :=
    (inferInstance : Module.Finite Γ(X, U.1) (AlgebraicGeometry.moduleSpecΓFunctor.obj G))
  let : Module.Projective Γ(X, U.1) Γ(G, ⊤) :=
    (inferInstance : Module.Projective Γ(X, U.1) (AlgebraicGeometry.moduleSpecΓFunctor.obj G))
  let eSect := affineSectionsLinearEquiv F U.2
  exact ⟨Module.Finite.equiv eSect,
    Module.Projective.of_equiv eSect⟩

private lemma rankAtStalk_sections_affineOpen
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d] (U : X.affineOpens) :
    ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk Γ(F, U.1) p = d := by
  let f := U.2.fromSpec
  let : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj F) d :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback f.base f.toRingCatSheafHom F
      d hF
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G d :=
    isFiniteLocallyFreeOfRank_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm d
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv (affineSectionsLinearEquiv F U.2)) p).symm.trans
    (moduleSpecΓ_rankAtStalk G d inferInstance p)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A determinant norm, with the power law whenever the morphism has constant rank.
The underlying map does not require a constant or positive rank. -/
structure DeterminantNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    extends MorphismNormMap f where
  /-- On affine opens where the algebra is finite free, the norm is its determinant norm. -/
  isDeterminantNorm : IsDeterminantNorm toMorphismNormMap
  /-- At constant rank `d`, the norm of a pulled-back function is its `d`-th power. -/
  app_pullback (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank f d]
    (U : Y.Opens) (g : Γ(Y, U)) : app U (f.app U g) = g ^ d

/-- The canonical determinant norm of Tag 0BD2 exists, and on an affine open of the target it
is `Algebra.projectiveNorm`, the determinant of multiplication. -/
private lemma exists_determinantNorm
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Morphisms.IsFiniteLocallyFree f] :
    ∃ N : DeterminantNorm f, ∀ (U : Y.affineOpens),
      letI := (f.app U.1).hom.toAlgebra
      ∀ (_ : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
        (_ : Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
        (s : Γ(X, f ⁻¹ᵁ U.1)),
        N.app U.1 s = Algebra.projectiveNorm Γ(Y, U.1) s := by
  refine ⟨{
    app := normApp f
    naturality := normApp_naturality f
    app_eq_zero_at_image := normApp_eq_zero_at_image f
    isDeterminantNorm := ?_
    app_pullback := normApp_pullback f }, ?_⟩
  · intro U hU _ _ _ s
    rw [normApp_affine f ⟨U, hU⟩]
    exact affineLocalNorm_eq_norm_of_free f ⟨U, hU⟩ inferInstance inferInstance s
  · intro U _ _ s
    exact normApp_affine f U s

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Stacks Project, Tag 0BD2.** The canonical determinant norm constructed in the proof,
for an arbitrary finite locally free morphism, including varying and zero rank.

Its defining property is `finiteLocallyFreeNorm_app_affine_eq_projectiveNorm`: on an affine
open of the target it is the determinant of multiplication. Taken with the two fields of
`DeterminantNorm` — the determinant formula on affine opens where the algebra is free, and the
power law at constant rank — this pins the norm down. -/
@[stacks 0BD2 "the canonical norm", ega "II 6.5.1" "special case", sga "3 V 4.1.1" "more general"]
noncomputable def finiteLocallyFreeNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Morphisms.IsFiniteLocallyFree f] : DeterminantNorm f :=
  Classical.choose (show ∃ N : DeterminantNorm f, ∀ (U : Y.affineOpens),
    let := (f.app U.1).hom.toAlgebra
    ∀ (_ : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (_ : Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (s : Γ(X, f ⁻¹ᵁ U.1)),
      N.app U.1 s = Algebra.projectiveNorm Γ(Y, U.1) s from by
        exact exists_determinantNorm f)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- On an affine open `U` of the target over which `Γ(X, f⁻¹U)` is finite projective, the
canonical norm is `Algebra.projectiveNorm`, the determinant of multiplication. -/
@[sga "3 V 4.1.1" "more general"]
theorem finiteLocallyFreeNorm_app_affine_eq_projectiveNorm
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (_ : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (_ : Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (s : Γ(X, f ⁻¹ᵁ U.1)),
      (finiteLocallyFreeNorm f).app U.1 s = Algebra.projectiveNorm Γ(Y, U.1) s := by
  let := (f.app U.1).hom.toAlgebra
  intro hfin hproj s
  exact Classical.choose_spec (exists_determinantNorm f) U hfin hproj s

private lemma finiteLocallyFreeNorm_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Morphisms.IsFiniteLocallyFree f]
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    (finiteLocallyFreeNorm f).app U s = normApp f U s := by
  apply section_eq_of_affine_restrictions
  intro V i
  rw [← (finiteLocallyFreeNorm f).naturality, ← normApp_naturality]
  let := (f.app V.1).hom.toAlgebra
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := inferInstance
  let : (Morphisms.pushforwardStructureSheaf f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  have h := finiteProjective_sections_affineOpen
    (Morphisms.pushforwardStructureSheaf f) inferInstance V
  rw [finiteLocallyFreeNorm_app_affine_eq_projectiveNorm f V h.1 h.2, normApp_affine f V]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Stacks Project, Tag 0BD2.** At positive constant rank `d`, the canonical determinant
norm is a norm of degree `d` in the sense of the Norms section. -/
@[stacks 0BD2 "the norm of positive constant degree", ega "II 6.5.1" "special case"]
noncomputable def finiteLocallyFreeNormOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank f d] (_hd : 0 < d) :
    {N : MorphismNorm f d // IsDeterminantNorm N.toMorphismNormMap} := by
  let := Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
  let N := finiteLocallyFreeNorm f
  exact ⟨{ toMorphismNormMap := N.toMorphismNormMap, app_pullback := N.app_pullback d },
    N.isDeterminantNorm⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Compatibility of the canonical determinant norm with an arbitrary cartesian base-change
square, when the base-changed morphism is finite locally free.

This is the content of Tag 0BD2's base-change clause; the clause itself additionally asserts
that `f'` *is* finite locally free, which is base-change stability of
`Stacks.Morphisms.IsFiniteLocallyFree`, the instance
`Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange`.
The clause itself is `Stacks.Divisors.finiteLocallyFreeNorm_baseChange`. -/
@[sga "4½ Sommes_trig 4.6" "partial"]
theorem finiteLocallyFreeNorm_app_baseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [Morphisms.IsFiniteLocallyFree f] [Morphisms.IsFiniteLocallyFree f']
    (sq : IsPullback g' f' f g) (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    (finiteLocallyFreeNorm f').app (g ⁻¹ᵁ U)
        (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
          intro x hx
          change f (g' x) ∈ U
          rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
          exact hx) s) =
      g.app U ((finiteLocallyFreeNorm f).app U s) := by
  simpa only [finiteLocallyFreeNorm_app] using normApp_baseChange f f' g' g sq U s

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The positive constant-rank case of `finiteLocallyFreeNorm_app_baseChange`: the degree-`d`
norm of the base change computes the base change of the degree-`d` norm, when the base-changed
morphism is finite locally free of rank `d`. -/
theorem finiteLocallyFreeNormOfRank_app_baseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank f d] [Morphisms.IsFiniteLocallyFreeOfRank f' d]
    (hd : 0 < d) (sq : IsPullback g' f' f g) (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    (finiteLocallyFreeNormOfRank f' d hd).1.app (g ⁻¹ᵁ U)
        (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
          intro x hx
          change f (g' x) ∈ U
          rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
          exact hx) s) =
      g.app U ((finiteLocallyFreeNormOfRank f d hd).1.app U s) := by
  let : Morphisms.IsFiniteLocallyFree f :=
    Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
  let : Morphisms.IsFiniteLocallyFree f' :=
    Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f' d
  simpa [finiteLocallyFreeNormOfRank] using
    finiteLocallyFreeNorm_app_baseChange f f' g' g sq U s

end Stacks.Divisors

end

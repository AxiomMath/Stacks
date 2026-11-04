module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inputs to the norm of a finite locally free morphism

A finite locally free morphism has a canonical determinant norm, including when its rank varies
or is zero. That norm, and its compatibility with base change, are
`Stacks.Norm.finiteLocallyFreeNorm` and `Stacks.Norm.finiteLocallyFreeNorm_baseChange` of
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm`, which this file imports. What
is proved here are the algebra-level and module-level inputs that construction consumes: the
projective determinant norm of a finite projective algebra, its multiplicativity, base change
and free-module comparison, and the finite locally free pullback and section data.

## Main definitions

* `finiteProjectiveAlgebraNorm` is the determinant norm of a finite projective algebra.
* `moduleSpec` and `finiteLocallyFreePullbackData` are the module-level inputs to the
  construction.

## Main results

* `finiteProjectiveAlgebraNorm_baseChange` and `finiteProjectiveAlgebraNorm_mul` are the
  compatibilities the sheaf-level norm is glued from.
* `baseChange_isFiniteLocallyFree` and `baseChange_isFiniteLocallyFreeOfRank` are the stability
  statements its base-change compatibility rests on.

## Implementation notes

The determinant construction works without a constant positive rank, as also used in Stacks Tag
0BW8; its positive constant-rank specialization has the norm properties of Stacks Tag 0BD2, and
both live in the Norm module named above rather than here.

The norm vocabulary (`Stacks.AlgebraicGeometry.MorphismNormMap`,
`Stacks.AlgebraicGeometry.MorphismNorm`) is Stacks Tag 0BD1's and lives in
`StacksDraft.AlgebraicGeometry.F3.FiniteLocallyFreeNorm.Defs`.

The two external inputs are the quasi-coherence of the direct image along an affine morphism and
the affine base-change isomorphism, both of Stacks Tag 02KG and both available in this library
(`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom` and
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`). Stability
of `Stacks.Morphisms.IsFiniteLocallyFree` under base change is proved here, in both the rank-free
and the fixed-rank form, rather than assumed.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TensorProduct TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.FiniteLocallyFreeNorm

open Stacks.Norm

@[sga "3 V 4.1"]
private noncomputable def finiteProjectiveAlgebraNorm {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] : A → R := fun a =>
  ProjectiveDeterminant.det (Algebra.lmul R A a)

private lemma finiteProjectiveAlgebraNorm_mul {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] (a b : A) :
    finiteProjectiveAlgebraNorm (R := R) (A := A) (a * b) =
      finiteProjectiveAlgebraNorm a * finiteProjectiveAlgebraNorm b := by
  change ProjectiveDeterminant.det (Algebra.lmul R A (a * b)) = _
  rw [show Algebra.lmul R A (a * b) =
      (Algebra.lmul R A b).comp (Algebra.lmul R A a) by
    ext x
    change a * b * x = b * (a * x)
    ring]
  simpa [finiteProjectiveAlgebraNorm, mul_comm] using (ProjectiveDeterminant.det_comp
    (Algebra.lmul R A a) (Algebra.lmul R A b))

private alias projectiveDeterminant_det_id := ProjectiveDeterminant.det_id

private lemma finiteProjectiveAlgebraNorm_one {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] :
    finiteProjectiveAlgebraNorm (R := R) (A := A) 1 = 1 := by
  change ProjectiveDeterminant.det (Algebra.lmul R A 1) = 1
  have hmul : (Algebra.lmul R A 1 : A →ₗ[R] A) = LinearMap.id := by
    ext x
    change (1 : A) * x = x
    simp
  rw [hmul, projectiveDeterminant_det_id]

@[sga "3 V 4.1"]
private noncomputable def finiteProjectiveAlgebraNormHom {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] : A →* R where
  toFun := finiteProjectiveAlgebraNorm
  map_one' := finiteProjectiveAlgebraNorm_one
  map_mul' := finiteProjectiveAlgebraNorm_mul

private lemma finiteProjectiveAlgebraNorm_eq_norm_of_free {R A : Type u}
    [CommRing R]
    [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A]
    (a : A) :
    finiteProjectiveAlgebraNorm (R := R) (A := A) a = Algebra.norm R a := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · let b := Module.finBasis R A
    rw [finiteProjectiveAlgebraNorm, ProjectiveDeterminant.det_eq_linearMap_det_of_basis b,
      Algebra.norm_eq_matrix_det b, ← LinearMap.det_toMatrix b, ← Algebra.toMatrix_lmul_eq b a]
    have hmul : (Algebra.lmul R A a : A →ₗ[R] A) = LinearMap.mulLeft R a := by
      ext x
      rfl
    rw [hmul]

private alias projectiveDeterminant_det_stabilize := ProjectiveDeterminant.det_stabilize

private alias projectiveDeterminant_det_baseChange := ProjectiveDeterminant.det_baseChange

private alias projectiveDeterminant_det_smul_id_of_rank :=
    ProjectiveDeterminant.det_smul_id_of_rankAtStalk

private lemma finiteProjectiveAlgebraNorm_algebraMap_of_rank {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] {d : ℕ}
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A p = d) (r : R) :
    finiteProjectiveAlgebraNorm (R := R) (A := A) (algebraMap R A r) = r ^ d := by
  change ProjectiveDeterminant.det (Algebra.lmul R A (algebraMap R A r)) = _
  have hmul : (Algebra.lmul R A (algebraMap R A r) : A →ₗ[R] A) =
      r • (LinearMap.id : A →ₗ[R] A) := by
    ext x
    change algebraMap R A r * x = r • x
    simp [Algebra.smul_def]
  rw [hmul]
  exact projectiveDeterminant_det_smul_id_of_rank hRank r

private alias module_rankAtStalk_eq_of_isFiniteLocallyFreeOfRank :=
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank

private lemma finiteProjectiveAlgebraNorm_baseChange {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] (b : B) :
    finiteProjectiveAlgebraNorm (R := A) (A := A ⊗[R] B)
        ((1 : A) ⊗ₜ[R] b) =
      algebraMap R A (finiteProjectiveAlgebraNorm (R := R) (A := B) b) := by
  classical
  have hmul :
      (Algebra.lmul A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b) :
        (A ⊗[R] B) →ₗ[A] (A ⊗[R] B)) =
        (Algebra.lmul R B b).baseChange A := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        simp only [LinearMap.baseChange_tmul]
        change ((1 : A) ⊗ₜ[R] b) * (a ⊗ₜ[R] x) = a ⊗ₜ[R] (b * x)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  change ProjectiveDeterminant.det
      (Algebra.lmul A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)) =
    algebraMap R A (ProjectiveDeterminant.det (Algebra.lmul R B b))
  rw [hmul]
  exact (projectiveDeterminant_det_baseChange (Algebra.lmul R B b)).symm

private alias projectiveDeterminant_det_conj := ProjectiveDeterminant.det_conj

private lemma finiteProjectiveAlgebraNorm_algEquiv {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₐ[R] B) (a : A) :
    finiteProjectiveAlgebraNorm (R := R) (A := B) (e a) =
      finiteProjectiveAlgebraNorm (R := R) (A := A) a := by
  change ProjectiveDeterminant.det (Algebra.lmul R B (e a)) =
    ProjectiveDeterminant.det (Algebra.lmul R A a)
  have hm : (Algebra.lmul R B (e a) : B →ₗ[R] B) =
      e.toLinearEquiv.toLinearMap.comp
        ((Algebra.lmul R A a).comp e.toLinearEquiv.symm.toLinearMap) := by
    ext b
    change e a * b = e (a * e.symm b)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [hm]
  exact projectiveDeterminant_det_conj e.toLinearEquiv (Algebra.lmul R A a)

private lemma schemeModules_isFiniteLocallyFree_of_card
    {X : Scheme.{u}} (F : X.Modules)
    (h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    Scheme.Modules.IsFiniteLocallyFree F := by
  classical
  obtain ⟨q, hfree, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  intro x
  have hx : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff _ _).1 q.coversTop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let T := (Scheme.Modules.overEquiv (q.X i)).functor
  let eFree := finiteFreeOverEquivIsoX X (q.X i) (q.generators i).I
  have : IsIso (q.generators i).π := hfree.isIso i
  let ePi : SheafOfModules.free (q.generators i).I ≅ F.over (q.X i) :=
    asIso (q.generators i).π
  let e : (Scheme.Modules.restrictFunctor (Scheme.Opens.ι (q.X i))).obj F ≅
      SheafOfModules.free (q.generators i).I :=
    ((Scheme.Modules.overFunctorEquiv (q.X i)).app F).symm ≪≫
      T.mapIso ePi.symm ≪≫ eFree.symm
  have := hfinite.isFiniteType i
  exact ⟨q.X i, hi, (q.generators i).I, inferInstance, ⟨e⟩⟩

private lemma tilde_isFiniteLocallyFreeOfRank_of_card
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (d : ℕ)
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (AlgebraicGeometry.moduleSpecΓFunctor.obj F))).IsFiniteLocallyFreeOfRank d :=
    by
  classical
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  have hfrom : IsIso (F.fromTildeΓ) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) F
  let e : AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hfrom
  intro x
  obtain ⟨q, hfree, hrank⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  have hx : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff _ _).1 q.coversTop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := q.X i
  let T := (Scheme.Modules.overEquiv U).functor
  let eFree := finiteFreeOverEquivIsoX (Spec (CommRingCat.of R)) U (q.generators i).I
  have : IsIso (q.generators i).π := hfree.isIso i
  let ePi : SheafOfModules.free (q.generators i).I ≅ F.over U :=
    asIso (q.generators i).π
  let eLocal : F.restrict (Scheme.Opens.ι U) ≅
      SheafOfModules.free (q.generators i).I :=
    ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
      T.mapIso ePi.symm ≪≫ eFree.symm
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
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    Module.IsFiniteLocallyFreeOfRank R (AlgebraicGeometry.moduleSpecΓFunctor.obj F) d :=
  (tilde_isFiniteLocallyFreeOfRank_iff R (AlgebraicGeometry.moduleSpecΓFunctor.obj F) d).mp
    (tilde_isFiniteLocallyFreeOfRank_of_card F d hF)

private lemma moduleSpecΓ_rankAtStalk_of_card
    {R : Type u} [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
    [F.IsQuasicoherent] (d : ℕ)
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d) :
    ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (AlgebraicGeometry.moduleSpecΓFunctor.obj F) p = d :=
  module_rankAtStalk_eq_of_isFiniteLocallyFreeOfRank d
    (moduleSpecΓ_isFiniteLocallyFreeOfRank F d hF)

/-- The pushforward functor on sheaves of modules along the ring-sheaf morphism underlying a
morphism of schemes is a right adjoint. Mathlib has this for `Scheme.Modules.pushforward`, which
is a `def` equal to this functor; instance search runs at reducible transparency and does not see
through that `def`, so the instance is restated here. -/
private instance isRightAdjoint_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint

/-- The pullback of the structure sheaf is the structure sheaf. This is Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, an isomorphism because the inverse-image functor on opens
is final; the instance is applied explicitly because instance search does not see through
`AlgebraicGeometry.Scheme.ringCatSheaf`. -/
@[ega "0 5.4.5" "special case"]
private lemma pullback_unit_map_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingCatSheafHom) :=
  have : (Opens.map f.base).Final :=
    Stacks.AlgebraicGeometry.ComponentDegrees.opensMap_final f.base
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u, u, u, u, u} f.toRingCatSheafHom

/-- Pushing generating sections forward along an isomorphism keeps them a free presentation. -/
private lemma isIso_ofEpi_π {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) (p : M ⟶ N) [IsIso p] [IsIso σ.π] : IsIso (σ.ofEpi p).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ σ.π p ‹_› ‹_›

/-- Finite local freeness depends only on the isomorphism class of a module. -/
private lemma schemeModule_finiteLocallyFree_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N)
    (hM : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N := by
  obtain ⟨q, hfree, hfinite⟩ := hM.exists_isFiniteLocallyFreeData
  let q' : SheafOfModules.LocalGeneratorsData.{u} N := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  have hfree' : q'.IsLocallyFreeData := ⟨fun i => by
    have : IsIso (q.generators i).π := hfree.isIso i
    exact isIso_ofEpi_π (q.generators i) _⟩
  have hfinite' : q'.IsFiniteType := ⟨fun i => ⟨(hfinite.isFiniteType i).finite⟩⟩
  exact { exists_isFiniteLocallyFreeData := ⟨q', hfree', hfinite'⟩ }

/-- The pullback of a finite locally free module is finite locally free. The slice-by-slice
transport of the local generating sections is
`Stacks.AlgebraicGeometry.ComponentDegrees.exists_pullbackOver`; this is its rank-free
counterpart to `Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData`. -/
private theorem finiteLocallyFreePullbackData {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (M : SheafOfModules.{u} S)
    (h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((SheafOfModules.pullback φ).obj M) := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  choose G hG eUnit eM using fun i ↦
    Stacks.AlgebraicGeometry.ComponentDegrees.exists_pullbackOver f φ M (q.X i)
  refine { exists_isFiniteLocallyFreeData := ⟨{
      I := q.I
      X := fun i ↦ (Opens.map f).obj (q.X i)
      coversTop := (Opens.coversTop_iff _ _).2
        (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
      generators := fun i ↦
        ((q.generators i).map (G i) (eUnit i).some).ofEpi (eM i).some.hom }, ?_, ?_⟩ }
  · refine ⟨fun i => ?_⟩
    have : IsIso (q.generators i).π := hq.isIso i
    exact isIso_ofEpi_π ((q.generators i).map (G i) (eUnit i).some) _
  · refine ⟨fun i => ?_⟩
    have : (q.generators i).IsFiniteType := hfin.isFiniteType i
    infer_instance

/-- The pullback of a finite locally free module along a morphism of schemes is finite locally
free. -/
private lemma pullback_isFiniteLocallyFree {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback g).obj M) :=
  finiteLocallyFreePullbackData g.base g.toRingCatSheafHom M h

/-- For a cartesian square whose right-hand morphism is affine, the pullback along the base
change of `f_* 𝒪_X` is `f'_* 𝒪_{X'}`. This is the affine base-change isomorphism of Stacks Tag
02KG at the unit module, followed by the identification of the pullback of the unit module with
the unit module. -/
@[ega "I 10.14.6" "special case"]
private noncomputable def pushforwardStructureSheaf_baseChangeIso
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S} (sq : IsPullback g' f' f g) [IsAffineHom f] :
    (Scheme.Modules.pullback g).obj (Stacks.Morphisms.pushforwardStructureSheaf f) ≅
      Stacks.Morphisms.pushforwardStructureSheaf f' :=
  have hUnitIso : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} g'.toRingCatSheafHom) :=
    pullback_unit_map_isIso g'
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := inferInstance
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w).app
      (SheafOfModules.unit X.ringCatSheaf)) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      sq (SheafOfModules.unit X.ringCatSheaf)
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w).app
      (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward f').mapIso
      (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} g'.toRingCatSheafHom) hUnitIso)

/-- Being finite locally free of rank `r` is stable under arbitrary base change. -/
@[ega "IV 21.15.8" "special case"]
private lemma baseChange_isFiniteLocallyFreeOfRank
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S} (sq : IsPullback g' f' f g) (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank f' r := by
  have : IsAffineHom f := h.toIsAffineHom
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj (Stacks.Morphisms.pushforwardStructureSheaf f)) r :=
    Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData g.base g.toRingCatSheafHom _ r
      h.toIsFiniteLocallyFreeOfRank
  have : IsAffineHom f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq h.toIsAffineHom
  exact .mk (toIsAffineHom := inferInstance)
    (toIsFiniteLocallyFreeOfRank :=
      (_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        (pushforwardStructureSheaf_baseChangeIso sq) inferInstance))

/-- Being finite locally free is stable under arbitrary base change, with no constant rank. -/
@[ega "IV 21.15.8" "more general"]
private lemma baseChange_isFiniteLocallyFree
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [h : Stacks.Morphisms.IsFiniteLocallyFree f] :
    Stacks.Morphisms.IsFiniteLocallyFree f' := by
  have : IsAffineHom f := h.toIsAffineHom
  have : IsAffineHom f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq h.toIsAffineHom
  exact .mk (toIsAffineHom := inferInstance)
    (toIsFiniteLocallyFree := schemeModule_finiteLocallyFree_of_iso
      (pushforwardStructureSheaf_baseChangeIso sq)
      (pullback_isFiniteLocallyFree g _ h.toIsFiniteLocallyFree))

private lemma finiteProjective_sections_of_card_affineOpen
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) ∧
      Module.Projective Γ(X, U.1) Γ(F, U.1) := by
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  have hG : Scheme.Modules.IsFiniteLocallyFree G :=
    schemeModules_isFiniteLocallyFree_of_card G <| schemeModule_finiteLocallyFree_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm
      (pullback_isFiniteLocallyFree f F hF)
  have : Module.Finite Γ(X, U.1) Γ(G, ⊤) :=
    (moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree G hG).1
  have : Module.Projective Γ(X, U.1) Γ(G, ⊤) :=
    (moduleSpecΓ_finite_and_projective_of_isFiniteLocallyFree G hG).2
  let eSect := affineSectionsLinearEquiv F U.2
  exact ⟨Module.Finite.equiv eSect, Module.Projective.of_equiv eSect⟩

private lemma finiteProjectiveAlgebraNorm_pushout
    {R A S B : CommRingCat.{u}} (i : R ⟶ A) (j : R ⟶ S)
    (k : A ⟶ B) (l : S ⟶ B) (h : IsPushout i j k l) :
    letI := i.hom.toAlgebra
    letI := l.hom.toAlgebra
    ∀ [Module.Finite R A] [Module.Projective R A]
      [Module.Finite S B] [Module.Projective S B] (a : A),
      finiteProjectiveAlgebraNorm (R := S) (k a) =
        j (finiteProjectiveAlgebraNorm (R := R) a) := by
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := l.hom.toAlgebra
  intro _ _ _ _ a
  let e := ((CommRingCat.isPushout_tensorProduct R S A).isoIsPushout S A h.flip)
  let e' : S ⊗[R] A ≃ₐ[S] B := {
    __ := e.commRingCatIsoToRingEquiv
    commutes' s := congr($( (CommRingCat.isPushout_tensorProduct R S A).inl_isoIsPushout_hom
      S A h.flip) s) }
  have hea : e' (1 ⊗ₜ[R] a) = k a :=
    congr($( (CommRingCat.isPushout_tensorProduct R S A).inr_isoIsPushout_hom
      S A h.flip) a)
  rw [← hea, finiteProjectiveAlgebraNorm_algEquiv,
    finiteProjectiveAlgebraNorm_baseChange]
  rfl

private lemma finiteProjectiveAlgebraNorm_eq_zero_of_field_hom
    {R A K L : Type u} [CommRing R] [CommRing A] [Field K] [Field L]
    [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    (j : R →+* K) (k : A →+* L) (l : K →+* L)
    (h : k.comp (algebraMap R A) = l.comp j) (a : A) (ha : k a = 0) :
    j (finiteProjectiveAlgebraNorm (R := R) a) = 0 := by
  let := j.toAlgebra
  let := l.toAlgebra
  let : Algebra R L := ((l.comp j).toAlgebra)
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let k' : A →ₐ[R] L := { __ := k, commutes' r := congr($h r) }
  let μ : K ⊗[R] A →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) k' (fun _ _ => Commute.all _ _)
  have hμ : μ (1 ⊗ₜ[R] a) = 0 := by simp [μ, ha, k']
  change algebraMap R K (finiteProjectiveAlgebraNorm (R := R) a) = 0
  rw [← finiteProjectiveAlgebraNorm_baseChange (R := R) (A := K),
    finiteProjectiveAlgebraNorm_eq_norm_of_free]
  change LinearMap.det (Algebra.lmul K (K ⊗[R] A) (1 ⊗ₜ[R] a)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr fun hker => ?_
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker) 1
  exact one_ne_zero <| calc
    (1 : L) = μ 1 := (map_one μ).symm
    _ = μ ((1 ⊗ₜ[R] a) * b) := congrArg μ hb.symm
    _ = 0 := by rw [map_mul, hμ, zero_mul]

private lemma rankAtStalk_sections_of_card_affineOpen
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)
    [hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F d]
    (U : X.affineOpens) :
    ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk Γ(F, U.1) p = d := by
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj F) d :=
    Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData f.base
      f.toRingCatSheafHom F d hF
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G d :=
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm inferInstance
  exact fun p => (congrFun (Module.rankAtStalk_eq_of_equiv
    (affineSectionsLinearEquiv F U.2)) p).symm.trans
      (moduleSpecΓ_rankAtStalk_of_card G d inferInstance p)

end Stacks.AlgebraicGeometry.FiniteLocallyFreeNorm

end
